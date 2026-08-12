#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
viral-radar : 한국 언더그라운드 바이럴 곡 조기 탐지

핵심 가설
---------
스포티파이 Viral 차트가 잡아주던 "빠르게 뜨고 빠르게 지는 곡"은
Shazam으로는 안 잡힌다. 숏폼 캡션에 이미 제목이 박혀서 돌기 때문에
아무도 "이 노래 뭐지?"를 찍지 않는다.

대신 그런 곡에는 공통 패턴이 있다:
    서로 무관한 여러 채널이 짧은 기간에 같은 곡의
    가사/1시간/슬로우 영상을 동시다발로 올린다.

조회수는 돈으로 살 수 있지만 "서로 모르는 채널 수"는 사기 어렵다.
그래서 이 도구는 조회수가 아니라 **서로 다른 채널 수의 증가 기울기**를 본다.

Shazam Top 200은 진입 신호가 아니라 '퇴장 신호'로 쓴다.
거기 이미 올라온 곡은 대중까지 넘어간 뒤라 커버 타이밍상 늦었다.
"""

import os
import re
import json
import math
import html
import sys
from datetime import datetime, timedelta, timezone

import requests
import time
import smtplib
from email.message import EmailMessage

# ---------------------------------------------------------------- 설정

KST = timezone(timedelta(hours=9))
API = "https://www.googleapis.com/youtube/v3"
KWORB_KR = "https://kworb.net/charts/shazam/kr.html"

STATE_PATH = "state/history.json"
REPORT_DIR = "reports"

# 탐색 창: 최근 N일 안에 올라온 영상만 본다 (오래된 곡 제외)
LOOKBACK_DAYS = 21

# 상위 몇 곡을 리포트에 실을지
TOP_N = 12

# 후보로 인정할 최소 (가중) 채널 수
MIN_CHANNELS = 2

# 제목에 한글이 없으면 버린다.
# 1차 실행에서 인도/힌디 'aesthetic lyrics status' 영상이 상위를 전부 먹었다.
# regionCode/relevanceLanguage 는 힌트일 뿐 필터가 아니라서 안 걸러진다.
REQUIRE_HANGUL = True

# 콘텐츠 팜 판정:
# 우리 표본 안에서 한 채널이 이 개수 이상의 서로 다른 곡을 올렸으면
# '가사 영상 공장'이다. 팬이 아니라 양산 채널이므로 표를 주지 않는다.
#
# 이게 이 도구의 핵심 방어선이다. "서로 다른 채널 수"라는 지표는
# 팜 채널들이 공짜로 위조할 수 있고, 1차 실행이 정확히 그렇게 뚫렸다.
FARM_SONGS_HARD = 6      # 이상이면 채널 자체를 무효표 처리
FARM_SONGS_SOFT = 3      # 이상이면 반 표만 인정

# 채널 독립성 검사:
# 4차 실행에서 '대파'와 '힙합팬타이탄'이 서로 다른 곡 여러 개에 나란히
# 등장했다. 신곡을 죄다 올리는 채널끼리는 늘 같이 다니므로, 그 둘이
# 한 곡에 모인 것은 우연이 아니고 따라서 아무 신호도 아니다.
#
# 이 지표의 전제는 '서로 모르는 채널들이 우연히 한 곡에 모인다'이다.
# 그래서 채널 수가 아니라 '독립적인 진영 수'를 센다.
# 표본 안에서 이 횟수 이상 함께 등장한 채널들은 한 진영으로 묶는다.
COOCCUR_BLOC = 2

# 본 표는 '지금 움직이는 곡'만 싣는다.
#
# 8/4 리포트에서 상위 5곡이 전부 진영 증가 +0.0에 진입 7~9일차였다.
# 이미 끝난 곡들이 그동안 쌓인 누적치로 순위표를 점거한 것이다.
# 형이 원하는 건 '지금 불붙는 곡'이지 '그동안 많이 쌓인 곡'이 아니다.
#
# 그래서 오늘 실제로 움직였는지를 본 표의 입장 조건으로 삼는다.
STALE_DAYS = 5          # 이 일수를 넘고
MIN_MOVE_CH = 0.5       # 진영 증가가 이 값 미만이면 본 표에서 뺀다
#
# 단, '오늘 실제로 다시 확인한 곡'에만 이 판정을 적용한다.
# 8/11 리포트에서 통과 0곡이 나온 원인이 이것이었다: 추적 중인 곡이
# 61개인데 2단 검증은 상위 20곡만 다시 봤고, 갱신되지 않은 41곡이
# '증가 0'으로 보여 전부 식은 곡으로 밀려났다.
# 안 본 것을 안 움직였다고 판정하면 안 된다.

# 본 표에 올리기 위한 최소 누적 조회수.
# 총 158회짜리가 2위에 오르는 건 바이럴이 아니라 잡음이다.
# 낮출수록 더 이른 시점을 잡지만 잡음도 늘어난다.
MIN_VIEWS = 800

# 검색어.
#
# 2차 실행 교훈: 1차 실패의 원인은 검색어가 아니라 필터였다.
# '가사', '1시간 가사' 같은 검색어는 가사 영상 생태계를 제대로 긁어오고
# 있었고, 인도계 양산물이 딸려온 게 문제였을 뿐이다. 그런데 필터를
# 고치면서 검색어까지 갈아엎었더니 이번엔 리액션/뉴스/쇼츠만 긁혀와서
# '같은 곡을 여러 채널이 올린다'는 패턴 자체가 표본에서 사라졌다.
#
# 한글 필터 + 팜 방어가 생겼으니 수확량 높은 검색어를 되살린다.
QUERIES = [
    # 넓은 그물 — 곡 '후보 이름'을 뽑는 용도. 정밀도는 2단에서 확보한다.
    "가사",
    "가사 lyrics",
    "1시간 가사",
    "슬로우 리버브 가사",
    "sped up 가사",
    "인디 노래 가사",
]

# 2단 검증에서 이름으로 다시 찾아볼 후보 곡 수 (조회수 상위부터)
#
# 검색 1회 = 100유닛, 하루 한도 10,000유닛.
# 40으로 잡았더니 1회 실행에 약 4,700유닛이 들어서 하루 두 번 돌리면
# 한도가 터졌다. 실제로 5차 실행이 그렇게 죽었고, 검색어가 전부 0건을
# 반환하는 바람에 '검색어 문제'로 오진할 뻔했다.
VERIFY_N = 45

# 조회수가 이보다 낮은 후보는 검증에 할당량을 쓰지 않는다
VERIFY_MIN_VIEWS = 100
# 곡 하나당 확인할 영상 수
VERIFY_MAX = 25

# 이 단어가 제목에 있으면 곡 자체가 아니라 파생/무관 콘텐츠다
JUNK_PATTERNS = [
    # 파생 콘텐츠
    "커버", "cover", "리액션", "reaction", "플레이리스트", "playlist",
    "메들리", "노래방", "챌린지", "안무", "댄스", "dance practice",
    "teaser", "티저", "노래모음", "모음", "컴필", "mashup", "매쉬업",
    "instrumental", "inst.", "mr 제거", "가이드보컬", "vocal cover",
    # 1차 실행에서 상위를 점령한 해외 양산 포맷
    "whatsapp", "status", "aesthetic", "shayari", "hindi", "punjabi",
    "bollywood", "lofi mix", "full song", "ringtone", "dj remix",
    "black screen", "bhojpuri", "telugu", "tamil", "lyrics loom",
    # 3차 실행에서 드러난 '가사'라는 단어만 들어간 잡담 영상
    "반응", "실수", "비밀", "레전드", "썰", "리뷰", "브이로그", "직캠",
    "교차편집", "무대", "연습", "몰카", "tmi", "멍청이", "가사 없는",
    "가사 못", "외우", "애교", "율동", "shorts #", "#shorts",
    "있다고", "이라고", "하는 노래", "그 노래", "노래는", "곱씹",
    "손글씨", "번역", "발음", "따라 부르기", "레벨",
    # 5차 표본에서 대량 유입된 힐링/종교/연속듣기 계열
    "연속듣기", "연속 듣기", "가사없는", "가사 없는", "명상", "힐링",
    "수면", "찬양", "ccm", "연주곡", "bgm", "asmr", "공부", "드라이브",
    "1시간 듣기", "1hour", "1 hour",
]

# 이 정도 구독자면 대형/기획사 채널로 본다
BIG_CHANNEL_SUBS = 1_000_000
MID_CHANNEL_SUBS = 100_000


# ---------------------------------------------------------------- 유틸

def log(msg):
    print(f"[{datetime.now(KST):%H:%M:%S}] {msg}", flush=True)


# API 오류 집계. 사유별로 나눠 센다 —
# '하루 총량 초과'와 '순간 속도 초과'는 원인도 대처도 완전히 다른데,
# 뭉쳐서 세다가 후자를 놓쳤다. 검색을 6번에서 32번으로 늘리면서
# 쉬는 시간 없이 연달아 쏘는 바람에 절반이 거절당하고 있었다.
API_ERRORS = {"quota": 0, "other": 0}
API_REASONS = {}

# 호출 사이 최소 간격(초). 순간 속도 제한을 피하기 위한 것.
CALL_GAP = 0.35
_last_call = [0.0]


def _throttle():
    wait = CALL_GAP - (time.time() - _last_call[0])
    if wait > 0:
        time.sleep(wait)
    _last_call[0] = time.time()


def yt(endpoint, key, retries=3, **params):
    """
    YouTube Data API 호출.

    일시적 거절(순간 속도 초과, 5xx)은 잠깐 쉬고 다시 시도한다.
    하루 총량 초과는 다시 시도해도 소용없으므로 즉시 포기한다.
    어떤 경우에도 예외를 던지지 않고 빈 결과를 돌려준다.
    """
    params["key"] = key
    delay = 1.0

    for attempt in range(retries):
        _throttle()
        try:
            r = requests.get(f"{API}/{endpoint}", params=params, timeout=30)
        except Exception as e:
            API_ERRORS["other"] += 1
            API_REASONS["network"] = API_REASONS.get("network", 0) + 1
            log(f"  ! {endpoint} 통신 실패: {e}")
            time.sleep(delay)
            delay *= 2
            continue

        if r.status_code == 200:
            return r.json()

        body = r.text[:400]
        reason = "unknown"
        m = re.search(r'"reason"\s*:\s*"([^"]+)"', body)
        if m:
            reason = m.group(1)
        API_REASONS[reason] = API_REASONS.get(reason, 0) + 1

        # 하루 총량 초과 — 재시도 무의미
        if reason in ("quotaExceeded", "dailyLimitExceeded"):
            API_ERRORS["quota"] += 1
            log(f"  !! 할당량 초과 — {endpoint} 거절")
            return {}

        # 일시적 — 쉬고 다시
        transient = (reason in ("rateLimitExceeded", "userRateLimitExceeded",
                                "backendError", "internalError")
                     or r.status_code >= 500 or r.status_code == 429)
        if transient and attempt < retries - 1:
            log(f"  ~ {endpoint} 일시 거절({reason}) — {delay:.0f}초 후 재시도")
            time.sleep(delay)
            delay *= 2
            continue

        API_ERRORS["other"] += 1
        log(f"  ! {endpoint} HTTP {r.status_code} ({reason})")
        return {}

    API_ERRORS["other"] += 1
    return {}


# ---------------------------------------------------------------- 제목 정규화

# 제목에서 걷어낼 장식들
BRACKET_RE = re.compile(r"[\[\(\{【（][^\]\)\}】）]*[\]\)\}】）]")
DECOR_RE = re.compile(
    r"((?<![가-힣])가사(?![가-힣])\s*(비디오)?|lyrics?|리릭\s*비디오|lyric\s*video|мv|official\s*(audio|video|mv)?"
    r"|audio|visualizer|비주얼라이저|1\s*시간|한시간|1\s*hour|loop|반복|"
    r"slowed(\s*\+?\s*reverb)?|reverb|슬로우(\s*리버브)?|sped\s*up|스페드업|"
    r"nightcore|8d|가사해석|해석|자막|kor\s*sub|번역|"
    r"노래제목으로|노래제목가사|노래제목|연속\s*재생|텍스트|texted|"
    r"신곡|정규|미니앨범|수록곡|타이틀곡|full\s*ver|色分け|color\s*coded)",
    re.IGNORECASE,
)
SPACE_RE = re.compile(r"\s+")
SEP_SPACED = re.compile(r"\s+[-–—|/·:]+\s+|\s*[|·:]\s*")
SEP_BARE = re.compile(r"\s*[-–—]\s*")


def split_parts(t):
    """공백을 낀 구분자를 우선한다. 로마자 표기의 하이픈을 보호하기 위함."""
    parts = SEP_SPACED.split(t)
    if len([p for p in parts if p.strip()]) >= 2:
        return parts
    return SEP_BARE.split(t)


# 붙어서 오는 합성 장식어는 한글 경계 규칙보다 먼저 통째로 지운다.
GLUED_RE = re.compile(r"노래제목(으로)?가사|가사영상|가사비디오|한글가사|가사해석",
                      re.IGNORECASE)


def clean_piece(s):
    s = GLUED_RE.sub(" ", s)
    s = BRACKET_RE.sub(" ", s)
    s = DECOR_RE.sub(" ", s)
    s = re.sub(r"[\"'“”‘’#♪♬★☆*ㅣ│｜┃⎮|]+", " ", s)
    s = SPACE_RE.sub(" ", s).strip(" -–—|/·:,.ㅣ│｜")
    return s


def parse_title(raw):
    """
    유튜브 제목에서 (아티스트, 곡명) 추출.
    실패하면 (None, None).

    실제로 흔한 형태들:
      "알프레도 - 긍정적 성격을 고쳐라 (가사)"
      "[가사] 무소치 - 가녀린 손가락에는 사탕 보석 반지 코어"
      "무소치 – 가녀린 손가락에는 사탕 보석 반지 코어 [1시간]"
    """
    t = html.unescape(raw or "")
    t = BRACKET_RE.sub(" ", t)          # 앞뒤 대괄호 장식 제거
    t = SPACE_RE.sub(" ", t).strip()

    parts = split_parts(t)
    parts = [clean_piece(p) for p in parts]
    parts = [p for p in parts if p and len(p) >= 2]

    if len(parts) < 2:
        return None, None

    artist, title = parts[0], parts[1]

    # 아티스트 자리에 문장 조각이 들어오는 사고 방지.
    # 예: "한 편의 영화같은 제니 신곡 - JENNIE" → 앞부분은 아티스트가 아니다.
    if len(artist) > 30 or len(title) > 60:
        return None, None
    if len(artist.split()) > 4:
        return None, None
    if re.search(r"(같은|신곡|노래|커버곡|모음|추천|리뷰|해석|후기|반응|영화|드라마)\s*$",
                 artist):
        return None, None
    if not artist or not title:
        return None, None

    return artist, title


def _n(s):
    s = (s or "").lower()
    return re.sub(r"[^0-9a-z가-힣ぁ-んァ-ン一-龥]", "", s)


# 제목 끝에 아티스트 이름이 다시 붙는 경우가 흔하다.
# "JENNIE - Less than a Lover 제니 신곡" → 장식어 '신곡'을 떼도 '제니'가 남아
# "제니 - Less than a Lover" 와 다른 곡으로 갈린다.
# 곡명 끝의 1~2 어절이 표본 안에서 아티스트로 쓰인 적 있으면 떼어낸다.
ARTIST_POOL = set()


def strip_trailing_artist(title):
    words = title.split()
    for take in (2, 1):
        if len(words) > take:
            tail = _n(" ".join(words[-take:]))
            if tail and tail in ARTIST_POOL:
                return " ".join(words[:-take])
    return title


def norm_key(artist, title):
    """
    같은 곡을 하나로 묶기 위한 키.

    아티스트명은 표기가 갈린다 — '알프레도' / 'Alfredo' / 'ALFREDO'.
    아티스트를 키에 넣으면 같은 곡이 쪼개져서 채널 수가 분산되고,
    채널 수가 이 도구의 핵심 지표라 순위가 통째로 망가진다.

    그래서 곡명이 충분히 길면(정규화 6자 이상) 곡명만으로 묶는다.
    짧고 흔한 제목('Love', 'Rain')만 아티스트를 함께 쓴다.
    """
    nt, na = _n(title), _n(artist)
    if len(nt) >= 6:
        return nt
    return f"{na}|{nt}"


def is_junk(raw):
    low = (raw or "").lower()
    return any(p in low for p in JUNK_PATTERNS)


# ---------------------------------------------------------------- 수집

def _absorb(seen, items):
    for it in items:
        vid = (it.get("id") or {}).get("videoId")
        sn = it.get("snippet") or {}
        if not vid or vid in seen:
            continue
        seen[vid] = {
            "videoId": vid,
            "title": html.unescape(sn.get("title", "")),
            "channelId": sn.get("channelId", ""),
            "channelTitle": html.unescape(sn.get("channelTitle", "")),
            "publishedAt": sn.get("publishedAt", ""),
        }


def collect_candidates(key):
    """검색어들을 돌면서 최근 업로드 영상 수집."""
    after = (datetime.now(timezone.utc) - timedelta(days=LOOKBACK_DAYS)).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )
    seen = {}
    stats = {}

    # 검색어마다 두 가지 순서로 긁는다.
    #
    # 왜: order=date + 50건은 '최근 한두 시간'만 보여준다. 유튜브에
    # '가사'가 들어간 영상은 시간당 수십 개씩 올라오기 때문이다.
    # 그런데 우리가 찾는 뭉침은 며칠에 걸쳐 벌어진다.
    # 백테스트에서 7/17 하루에 채널 27개가 붙은 급증을 우리 스캐너가
    # 통째로 놓친 이유가 정확히 이것이었다. 창문이 한 시간짜리였다.
    #
    # order=viewCount 를 같이 돌려서 '기간 안에서 실제로 조회수가 붙은 것'을
    # 함께 본다. 이쪽은 업로드 시각과 무관하게 걸린다.
    for q in QUERIES:
        got = 0
        for order in ("date", "viewCount"):
            data = yt(
                "search", key,
                part="snippet", q=q, type="video", order=order,
                regionCode="KR", relevanceLanguage="ko",
                publishedAfter=after, maxResults=50,
            )
            items = data.get("items", [])
            got += len(items)
            _absorb(seen, items)
        stats[q] = got
        log(f"  검색 '{q}' → {got}건 (date+viewCount)")
    return list(seen.values()), stats


def enrich_videos(key, vids):
    """조회수 붙이기. videos.list는 1유닛이라 저렴."""
    out = {}
    ids = [v["videoId"] for v in vids]
    for i in range(0, len(ids), 50):
        chunk = ids[i:i + 50]
        data = yt("videos", key, part="statistics", id=",".join(chunk), maxResults=50)
        for it in data.get("items", []):
            st = it.get("statistics") or {}
            out[it["id"]] = int(st.get("viewCount", 0) or 0)
    for v in vids:
        v["views"] = out.get(v["videoId"], 0)
    return vids


def enrich_channels(key, vids):
    """구독자 수 붙이기 — 언더그라운드 판정용."""
    subs = {}
    cids = sorted({v["channelId"] for v in vids if v["channelId"]})
    for i in range(0, len(cids), 50):
        chunk = cids[i:i + 50]
        data = yt("channels", key, part="statistics", id=",".join(chunk), maxResults=50)
        for it in data.get("items", []):
            st = it.get("statistics") or {}
            if st.get("hiddenSubscriberCount"):
                subs[it["id"]] = 0
            else:
                subs[it["id"]] = int(st.get("subscriberCount", 0) or 0)
    return subs


# ---------------------------------------------------------------- 2단 검증

def verify_candidates(key, songs, existing_ids, prev=None):
    """
    2단: 곡 이름으로 다시 검색해서 '그 곡을 올린 채널'을 제대로 센다.

    3차 실행에서 드러난 문제:
    넓은 검색어로 최근 영상 400여 건을 긁으면 곡이 400개 나온다.
    곡당 채널이 1개씩이라 '여러 채널이 같은 곡을 올린다'는 신호가
    구조적으로 잡힐 수가 없다. 그물이 넓고 얕아서 뭉침이 안 보인다.

    그래서 1단은 '곡 이름 뽑기'로만 쓰고,
    여기서 곡마다 이름으로 직접 다시 검색해 깊게 판다.
    """
    after = (datetime.now(timezone.utc) - timedelta(days=LOOKBACK_DAYS)).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )
    # 오늘 표본에서 뽑힌 후보
    pool = {s["key"]: s for s in songs.values()}

    # 어제까지 추적하던 곡도 반드시 다시 확인한다.
    #
    # 왜: 1단 표본은 매일 달라진다. 어제 잡힌 곡이 오늘 표본에 안 들어오면
    # 추적이 끊기고 '진영 증가'라는 핵심 지표가 계산되지 않는다.
    # 뭉침은 며칠에 걸쳐 벌어지므로 곡을 계속 붙들고 있어야 한다.
    for k, p in (prev or {}).items():
        if k in pool:
            continue
        if not p.get("artist") or not p.get("title"):
            continue
        pool[k] = {
            "key": k,
            "artist": p["artist"],
            "title": p["title"],
            "views": p.get("views", 0),
        }

    ranked = [s for s in pool.values() if s["views"] >= VERIFY_MIN_VIEWS]
    ranked.sort(key=lambda s: s["views"], reverse=True)
    ranked = ranked[:VERIFY_N]

    found, checked = [], set()
    for s in ranked:
        q = f"{s['artist']} {s['title']}"
        data = yt(
            "search", key,
            part="snippet", q=q, type="video", order="relevance",
            regionCode="KR", relevanceLanguage="ko",
            publishedAfter=after, maxResults=VERIFY_MAX,
        )
        items = data.get("items", [])
        hit = 0
        for it in items:
            vid = (it.get("id") or {}).get("videoId")
            sn = it.get("snippet") or {}
            if not vid or vid in existing_ids:
                continue
            title = html.unescape(sn.get("title", ""))
            if is_junk(title):
                continue
            a, t = parse_title(title)
            if not a or not t:
                continue
            # 같은 곡인지 확인 — 곡명 정규화가 일치해야 인정
            if norm_key(a, t) != s["key"]:
                continue
            existing_ids.add(vid)
            hit += 1
            found.append({
                "videoId": vid,
                "title": title,
                "channelId": sn.get("channelId", ""),
                "channelTitle": html.unescape(sn.get("channelTitle", "")),
                "publishedAt": sn.get("publishedAt", ""),
            })
        checked.add(s["key"])
        log(f"  검증 '{q[:34]}' → +{hit}건")

    return found, checked


# ---------------------------------------------------------------- Shazam 퇴장 필터

def fetch_shazam_kr():
    """
    kworb의 Shazam 한국 Top 200을 긁어서 정규화 키 집합으로 반환.
    여기 이미 있으면 = 대중까지 넘어감 = 커버 타이밍 늦음.
    """
    keys = set()
    try:
        r = requests.get(KWORB_KR, timeout=30,
                         headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code != 200:
            log(f"  ! kworb HTTP {r.status_code}")
            return keys
        cells = re.findall(r"<td[^>]*>(.*?)</td>", r.text, re.S)
        if not cells:
            # 마크업이 바뀌어도 죽지 않게: 태그 걷어내고 줄 단위로 훑는다
            cells = re.sub(r"<[^>]+>", "\n", r.text).split("\n")
        for cell in cells:
            txt = html.unescape(re.sub(r"<[^>]+>", "", cell)).strip()
            if " - " not in txt or len(txt) > 160:
                continue
            a, _, t = txt.partition(" - ")
            a, t = clean_piece(a), clean_piece(t)
            if a and t:
                keys.add(norm_key(a, t))
    except Exception as e:
        log(f"  ! kworb 실패: {e}")
    return keys


# ---------------------------------------------------------------- 집계 + 점수

HANGUL_RE = re.compile(r"[가-힣]")


def has_hangul(s):
    return bool(HANGUL_RE.search(s or ""))


def detect_farms(parsed):
    """
    콘텐츠 팜 판정.

    가사 영상 공장 채널은 하루에 수십 곡을 찍어낸다. 그런 채널이 여럿
    겹치면 우리 눈에는 '서로 다른 채널이 동시에 올렸다'로 보이지만,
    실제로는 유행과 아무 상관이 없다. 1차 실행이 이걸로 뚫렸다.

    한 채널이 표본 안에서 올린 '서로 다른 곡'의 수로 판정하고,
    채널마다 표의 무게를 다르게 준다.
    """
    per_channel = {}
    for p in parsed:
        per_channel.setdefault(p["channelId"], set()).add(p["key"])

    weights = {}
    for cid, keys in per_channel.items():
        n = len(keys)
        if n >= FARM_SONGS_HARD:
            weights[cid] = 0.0          # 무효표
        elif n >= FARM_SONGS_SOFT:
            weights[cid] = 0.5          # 반 표
        else:
            weights[cid] = 1.0          # 온전한 한 표
    return weights, per_channel


def build_blocs(parsed):
    """
    늘 붙어다니는 채널들을 하나의 '진영'으로 묶는다.

    표본 안에서 두 채널이 COOCCUR_BLOC 곡 이상 함께 등장하면
    독립된 출처로 보지 않는다. 유니온-파인드로 연결 성분을 만든다.
    """
    songs_of = {}
    for p in parsed:
        songs_of.setdefault(p["key"], set()).add(p["channelId"])

    pair = {}
    for chans in songs_of.values():
        cs = sorted(chans)
        for i in range(len(cs)):
            for j in range(i + 1, len(cs)):
                pair[(cs[i], cs[j])] = pair.get((cs[i], cs[j]), 0) + 1

    parent = {}

    def find(x):
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for (a, b), n in pair.items():
        if n >= COOCCUR_BLOC:
            union(a, b)

    return {c: find(c) for c in {p["channelId"] for p in parsed}}


def aggregate(vids, subs):
    """
    1차: 제목 파싱 + 정크/한글 필터
    2차: 아티스트-곡명 순서 교정
    3차: 곡 단위 묶기 (팜 채널 가중 반영)
    """
    # ---- 1차 --------------------------------------------------------
    drops = {"junk": 0, "nohangul": 0, "unparsed": 0}
    parsed = []
    for v in vids:
        if is_junk(v["title"]):
            drops["junk"] += 1
            continue
        # 한글 판정은 '원본 제목' 기준.
        # 파싱된 아티스트/곡명만 보면 'nephillm - ny2mia [가사]' 같은
        # 영문 표기 한국 곡이 통째로 날아간다. 원본에는 '가사'가 남아 있다.
        if REQUIRE_HANGUL and not has_hangul(v["title"]):
            drops["nohangul"] += 1
            continue
        artist, title = parse_title(v["title"])
        if not artist or not title:
            drops["unparsed"] += 1
            continue
        parsed.append({**v, "artist": artist, "title": title})

    # 표본에 등장한 아티스트 이름을 모아둔다 (꼬리 제거용)
    ARTIST_POOL.clear()
    for p in parsed:
        n = _n(p["artist"])
        if n:
            ARTIST_POOL.add(n)
    for p in parsed:
        p["title"] = strip_trailing_artist(p["title"]) or p["title"]

    # ---- 2차: 순서 교정 ---------------------------------------------
    # "Worry - LONOWN" 처럼 곡명이 앞에 오는 경우가 있다.
    # 표본 전체에서 각 문자열이 앞자리(아티스트 위치)에 얼마나 자주
    # 등장했는지 세어, 뒷자리 쪽이 더 '아티스트다우면' 뒤집는다.
    front = {}
    for p in parsed:
        n = _n(p["artist"])
        if n:
            front[n] = front.get(n, 0) + 1

    for p in parsed:
        a, t = _n(p["artist"]), _n(p["title"])
        if front.get(t, 0) > front.get(a, 0):
            p["artist"], p["title"] = p["title"], p["artist"]
        p["key"] = norm_key(p["artist"], p["title"])

    parsed = [p for p in parsed if p["key"] and len(p["key"]) >= 4]

    # ---- 팜 채널 가중치 + 진영 묶기 ---------------------------------
    weights, per_channel = detect_farms(parsed)
    blocs = build_blocs(parsed)

    # ---- 3차: 곡 단위 묶기 ------------------------------------------
    songs = {}
    for p in parsed:
        k = p["key"]
        s = songs.setdefault(k, {
            "key": k,
            "pair_votes": {},
            "channels": set(),
            "weighted_channels": 0.0,
            "videos": [],
            "views": 0,
            "max_subs": 0,
        })
        # 아티스트와 곡명은 반드시 '쌍'으로 투표한다.
        # 따로 뽑으면 A곡의 아티스트 + B곡의 제목이 조합되는 사고가 난다.
        pair = (p["artist"], p["title"])
        s["pair_votes"][pair] = s["pair_votes"].get(pair, 0) + 1
        s["channels"].add(p["channelId"])
        s["videos"].append(p)
        s["views"] += p.get("views", 0)
        s["max_subs"] = max(s["max_subs"], subs.get(p["channelId"], 0))

    for s in songs.values():
        # 득표 우선, 동률이면 한글 표기 우선
        best_pair = max(
            s["pair_votes"].items(),
            key=lambda kv: (kv[1], has_hangul(kv[0][0]) + has_hangul(kv[0][1]))
        )[0]
        s["artist"], s["title"] = best_pair
        # 같은 진영은 여러 채널이어도 한 표.
        # 진영 안에서 가장 높은 가중치만 인정한다.
        by_bloc = {}
        for c in s["channels"]:
            b = blocs.get(c, c)
            by_bloc[b] = max(by_bloc.get(b, 0.0), weights.get(c, 1.0))
        s["weighted_channels"] = sum(by_bloc.values())
        s["blocs"] = len(by_bloc)
        s["farm_channels"] = sum(1 for c in s["channels"] if weights.get(c, 1.0) == 0.0)

    return songs, drops


def score_songs(songs, prev, shazam_keys, today, checked=None):
    """
    점수 = 채널 증가 모멘텀 × 언더그라운드 가중 × 신선도
    조회수는 보조 지표로만 (로그 스케일).
    """
    results = []
    for k, s in songs.items():
        # 팜 채널을 걷어낸 '실질 채널 수'로 판정한다
        n_ch = s.get("weighted_channels", len(s["channels"]))

        p = prev.get(k, {})
        prev_ch = set(p.get("channels", []))
        prev_views = p.get("views", 0)
        first_seen = p.get("first_seen", today)

        # 신규 채널도 같은 비율로 환산 (팜이 새로 붙은 건 신호가 아니다)
        raw_total = max(1, len(s["channels"]))
        new_ch = len(s["channels"] - prev_ch) * (n_ch / raw_total)
        view_delta = max(0, s["views"] - prev_views)

        # 진입 며칠차
        try:
            d0 = datetime.strptime(first_seen, "%Y-%m-%d").date()
            days = (datetime.strptime(today, "%Y-%m-%d").date() - d0).days
        except Exception:
            days = 0

        # 모멘텀: 새 채널이 핵심, 조회수는 보조
        momentum = new_ch * 4.0 + n_ch * 1.0 + math.log10(view_delta + 1) * 1.5

        # 언더그라운드 가중: 대형 채널이 끼어 있으면 이미 판이 커진 것
        if s["max_subs"] >= BIG_CHANNEL_SUBS:
            under = 0.25
        elif s["max_subs"] >= MID_CHANNEL_SUBS:
            under = 0.6
        else:
            under = 1.0

        # 신선도: 오래 추적된 곡은 감쇠 (형 목적상 초기 창이 중요)
        # 3일까지는 온전히, 그 뒤로는 빠르게 식는다.
        # 형이 노리는 창은 폭발 1~3일차라 그 뒤 곡은 순위에서 밀려야 한다.
        fresh = 1.0 if days <= 3 else max(0.1, math.exp(-(days - 3) / 4.0))

        on_shazam = k in shazam_keys
        score = momentum * under * fresh
        if on_shazam:
            score *= 0.3   # 퇴장 신호 — 완전 제외는 안 하고 강하게 감점

        # 오늘 재확인하지 않은 곡은 '증가 0'이 관측이 아니라 무지다.
        # 그래서 식은 곡으로 몰지도 않고, 본 표에 올리지도 않는다.
        # 확인한 곡만 판정 대상이다 — 모르는 걸 안다고 하지 않는다.
        _checked = (checked is None) or (k in checked)
        _stale = _checked and days >= STALE_DAYS and new_ch < MIN_MOVE_CH

        best = max(s["videos"], key=lambda v: v.get("views", 0))

        results.append({
            "key": k,
            "artist": s["artist"],
            "title": s["title"],
            "score": round(score, 2),
            "channels": round(n_ch, 1),
            "raw_channels": len(s["channels"]),
            "farm_channels": s.get("farm_channels", 0),
            "new_channels": round(new_ch, 1),
            "views": s["views"],
            "view_delta": view_delta,
            "max_subs": s["max_subs"],
            "days": days,
            "first_seen": first_seen,
            "on_shazam": on_shazam,
            "passes": (_checked
                       and n_ch >= MIN_CHANNELS
                       and s["views"] >= MIN_VIEWS
                       and not _stale),
            "stale": _stale,
            "checked": _checked,
            "best_video": f"https://youtu.be/{best['videoId']}",
            "best_title": best["title"],
            "channel_names": sorted({v["channelTitle"] for v in s["videos"]})[:6],
        })

    results.sort(key=lambda r: r["score"], reverse=True)
    return results


# ---------------------------------------------------------------- 리포트

def fmt_num(n):
    if n >= 100_000_000:
        return f"{n/100_000_000:.1f}억"
    if n >= 10_000:
        return f"{n/10_000:.1f}만"
    return f"{n:,}"


def write_report(results, today, first_run, n_vids, n_songs, diag=None):
    os.makedirs(REPORT_DIR, exist_ok=True)
    path = f"{REPORT_DIR}/{today}.md"
    passing = [r for r in results if r.get("passes")]
    watch = [r for r in results if not r.get("passes") and not r.get("stale")]
    watch.sort(key=lambda r: r["view_delta"], reverse=True)
    top = passing[:TOP_N]

    L = []
    L.append(f"# 바이럴 레이더 — {today}")
    L.append("")
    L.append(f"수집 영상 {n_vids}건 · 곡 후보 {n_songs}곡 · "
             f"독립 진영 {MIN_CHANNELS}개 이상 + 조회 {MIN_VIEWS}회 이상 → {len(passing)}곡")
    L.append("")

    if (diag or {}).get("quota_errors"):
        L.append("> ## ⚠ 이 리포트는 신뢰하지 마")
        L.append(f"> **YouTube API 하루 할당량이 바닥나서 검색 "
                 f"{diag['quota_errors']}건이 거절됐어.**")
        L.append("> 곡이 적게 나온 건 실제로 조용해서가 아니라 데이터를 "
                 "못 긁어와서야.")
        L.append("> 할당량은 매일 한국시간 오후 4시쯤 초기화돼. 그 뒤에 다시 돌리면 돼.")
        L.append("")

    if first_run:
        L.append("> **첫 실행이라 이번 리포트는 기준선(baseline)이야.**")
        L.append("> 모든 곡이 '신규'로 잡히니까 순위는 아직 의미 없어.")
        L.append("> 내일부터 어제 대비 채널 증가가 계산되면서 진짜 순위가 나와.")
        L.append("")

    if not top:
        L.append("_오늘은 조건을 넘은 곡이 없어._")
    else:
        L.append("| # | 곡 | 진입 | 진영 | 어제比 | 조회수 | 최대구독 | Shazam |")
        L.append("|---|-----|------|------|--------|--------|----------|--------|")
        for i, r in enumerate(top, 1):
            flag = "⚠ 진입" if r["on_shazam"] else "—"
            L.append(
                f"| {i} | **{r['artist']} – {r['title']}** | {r['days']}일차 | "
                f"{r['channels']} | +{r['new_channels']} | {fmt_num(r['views'])} | "
                f"{fmt_num(r['max_subs'])} | {flag} |"
            )
        L.append("")
        L.append("---")
        L.append("")
        for i, r in enumerate(top, 1):
            L.append(f"### {i}. {r['artist']} – {r['title']}")
            L.append("")
            L.append(f"- 점수 **{r['score']}** · 진입 {r['days']}일차 "
                     f"(최초 포착 {r['first_seen']})")
            ch_line = (f"- 독립 진영 **{r['channels']}개** "
                       f"(어제 대비 +{r['new_channels']}, 원시 채널 {r['raw_channels']}개)")
            if r.get("farm_channels"):
                ch_line += f" · 원시 {r['raw_channels']}개 중 양산채널 {r['farm_channels']}개 제외"
            L.append(ch_line)
            L.append(f"- 누적 조회 {fmt_num(r['views'])} (오늘 +{fmt_num(r['view_delta'])})")
            L.append(f"- 최대 채널 규모 {fmt_num(r['max_subs'])} 구독")
            if r["on_shazam"]:
                L.append("- ⚠ **Shazam 한국 200 진입 — 이미 대중까지 넘어감. 커버 타이밍 늦었을 수 있음**")
            L.append(f"- 채널: {', '.join(r['channel_names'])}")
            L.append(f"- 대표 영상: [{r['best_title']}]({r['best_video']})")
            L.append("")

    # ── 식은 곡: 한때 잡혔지만 지금은 안 움직이는 곡 ────────────────
    stale = [r for r in results if r.get("stale")][:8]
    if stale:
        L.append("---")
        L.append("")
        L.append("## 식은 곡 (움직임 멈춤)")
        L.append("")
        L.append("_진영이 더 안 늘어. 참고용이고 노릴 구간은 지났어._")
        L.append("")
        for r in stale:
            L.append(f"- **{r['artist']} – {r['title']}** · {r['days']}일차 · "
                     f"진영 {r['channels']} · 조회 {fmt_num(r['views'])}")
        L.append("")

    # ── 관찰 목록: 아직 채널 1개지만 움직임이 있는 곡 ──────────────
    if watch:
        L.append("---")
        L.append("")
        L.append("## 관찰 중 (아직 채널 1개)")
        L.append("")
        L.append("_여기서 채널이 하나 더 붙으면 위 표로 올라온다._")
        L.append("")
        for r in watch[:15]:
            miss = []
            if r["channels"] < MIN_CHANNELS:
                miss.append(f"진영 {r['channels']}")
            if r["views"] < MIN_VIEWS:
                miss.append(f"조회 {fmt_num(r['views'])}")
            if not r.get("checked", True):
                why = "오늘 미확인"
            else:
                why = " · ".join(miss) if miss else "판정 보류"
            L.append(f"- **{r['artist']} – {r['title']}** · "
                     f"{r['days']}일차 · 조회 {fmt_num(r['views'])} · "
                     f"({why}) · [영상]({r['best_video']})")
        L.append("")

    # ── 진단: 검색어가 뭘 긁어오는지 눈으로 보기 위한 구역 ──────────
    if diag:
        L.append("---")
        L.append("")
        L.append("## 진단 (검색어 조정용)")
        L.append("")
        L.append("| 검색어 | 수확 |")
        L.append("|--------|------|")
        for q, c in (diag.get("queries") or {}).items():
            L.append(f"| `{q}` | {c} |")
        L.append("")
        L.append(f"2단 검증으로 추가 확보한 영상: {diag.get('verified',0)}건")
        L.append("")
        L.append(f"API 오류 — 할당량 초과 {diag.get('quota_errors',0)}건 · "
                 f"기타 {diag.get('api_errors',0)}건")
        reasons = diag.get("reasons") or {}
        if reasons:
            L.append("")
            L.append("거절 사유별: " + ", ".join(
                f"`{k}` {v}건" for k, v in
                sorted(reasons.items(), key=lambda kv: -kv[1])))
        L.append("")
        drops = diag.get("drops") or {}
        if drops:
            L.append("")
            L.append(f"걸러낸 영상 — 정크 {drops.get('junk',0)} · "
                     f"한글없음 {drops.get('nohangul',0)} · "
                     f"파싱실패 {drops.get('unparsed',0)}")
            L.append("")
        samples = diag.get("samples") or []
        if samples:
            L.append("실제로 긁혀온 제목 표본 20개:")
            L.append("")
            for t in samples[:20]:
                L.append(f"- {t}")
            L.append("")

    L.append("---")
    L.append("")
    L.append("**읽는 법** — `진영`은 채널 수가 아니라 *서로 무관한 출처가 몇 개인가*야. "
             "늘 같이 다니는 채널들은 한 진영으로 묶여서 한 표만 쳐. "
             "`어제比 +N`이 클수록 지금 불붙는 중이고, `진입 3일차` 이내 + 진영 급증이 형이 노릴 구간. "
             "`Shazam ⚠`가 붙으면 이미 대중까지 넘어가서 늦은 신호야.")
    L.append("")

    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(L))
    return path


def write_latest(path):
    """항상 같은 위치에서 최신 리포트를 볼 수 있게 복사."""
    try:
        with open(path, encoding="utf-8") as f:
            content = f.read()
        with open("LATEST.md", "w", encoding="utf-8") as f:
            f.write(content)
    except Exception as e:
        log(f"  ! LATEST.md 실패: {e}")



# ---------------------------------------------------------------- 메일 발송

def send_mail(results, today, quota_hit):
    """
    아침에 볼 톱5를 메일로 보낸다.

    빈 날에는 보내지 않는다. 알프레도급 급증은 몇 주에 한 번 일어나는
    사건이라 대부분의 날은 아무것도 안 잡히는 게 정상이고, 매일 빈 메일이
    오면 형이 메일 자체를 안 열게 된다.
    단, 할당량 초과처럼 '도구가 고장난' 경우는 반드시 알린다.
    """
    to = os.environ.get("MAIL_TO", "").strip()
    frm = os.environ.get("MAIL_FROM", "").strip()
    pw = os.environ.get("MAIL_APP_PASSWORD", "").strip()
    if not (to and frm and pw):
        log("메일 설정 없음 — 발송 건너뜀")
        return

    hits = [r for r in results if r.get("passes")][:5]
    if not hits and not quota_hit:
        log("오늘은 잡힌 곡 없음 — 메일 보내지 않음")
        return

    if quota_hit:
        subject = f"[바이럴 레이더] {today} 도구 점검 필요"
    else:
        top = hits[0]
        subject = (f"[바이럴 레이더] {today} — {top['artist']} 외 {len(hits)-1}곡"
                   if len(hits) > 1 else
                   f"[바이럴 레이더] {today} — {top['artist']}")

    rows = []
    for i, r in enumerate(hits, 1):
        late = ' <span style="color:#c0392b">늦음</span>' if r["on_shazam"] else ""
        rows.append(
            f"<tr>"
            f"<td style='padding:6px 10px'>{i}</td>"
            f"<td style='padding:6px 10px'><b>{r['artist']}</b> – {r['title']}{late}</td>"
            f"<td style='padding:6px 10px;text-align:center'>{r['days']}일차</td>"
            f"<td style='padding:6px 10px;text-align:center'>{r['channels']} "
            f"(+{r['new_channels']})</td>"
            f"<td style='padding:6px 10px;text-align:right'>{fmt_num(r['views'])}</td>"
            f"<td style='padding:6px 10px'>"
            f"<a href='{r['best_video']}'>듣기</a></td>"
            f"</tr>"
        )

    warn = ""
    if quota_hit:
        warn = ("<p style='background:#fdecea;padding:10px;border-radius:6px'>"
                "<b>API 하루 할당량이 바닥났어.</b> 오늘 결과는 신뢰하지 마. "
                "한국시간 오후 4시쯤 초기화돼.</p>")

    html = f"""<div style="font-family:-apple-system,'Apple SD Gothic Neo',sans-serif;
                            max-width:640px;color:#222">
      <h2 style="margin-bottom:4px">바이럴 레이더 · {today}</h2>
      {warn}
      <table style="border-collapse:collapse;width:100%;font-size:14px">
        <tr style="background:#f4f4f5;text-align:left">
          <th style="padding:6px 10px">#</th>
          <th style="padding:6px 10px">곡</th>
          <th style="padding:6px 10px">진입</th>
          <th style="padding:6px 10px">진영</th>
          <th style="padding:6px 10px">조회</th>
          <th style="padding:6px 10px"></th>
        </tr>
        {''.join(rows) if rows else "<tr><td colspan=6 style='padding:10px'>잡힌 곡 없음</td></tr>"}
      </table>
      <p style="font-size:13px;color:#666;margin-top:14px">
        <b>진영</b>은 채널 수가 아니라 서로 무관한 출처 수야.
        늘 같이 다니는 채널은 한 표로 접혀.
        <b>진입 3일차 이내 + 진영 급증</b>이 노릴 구간이고,
        <span style="color:#c0392b">늦음</span> 표시는 이미 Shazam 한국 200에
        올라서 대중까지 넘어갔다는 뜻이야.
      </p>
      <p style="font-size:12px;color:#999">
        전체 리포트는 저장소 LATEST.md 에 있어. 곡이 안 잡힌 날은 메일이 안 와.
      </p>
    </div>"""

    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = frm
    msg["To"] = to
    msg.set_content("HTML 메일이야. 텍스트만 보이면 저장소 LATEST.md 를 봐줘.")
    msg.add_alternative(html, subtype="html")

    host, _, port = os.environ.get("MAIL_SMTP", "smtp.gmail.com:587").partition(":")
    try:
        with smtplib.SMTP(host, int(port or 587), timeout=30) as s:
            s.starttls()
            s.login(frm, pw)
            s.send_message(msg)
        log(f"메일 발송 완료 → {to} ({len(hits)}곡)")
    except Exception as e:
        log(f"! 메일 발송 실패: {e}")


# ---------------------------------------------------------------- 상태 저장

def load_state():
    if not os.path.exists(STATE_PATH):
        return {}, True
    try:
        with open(STATE_PATH, encoding="utf-8") as f:
            return json.load(f), False
    except Exception:
        return {}, True


def save_state(songs, prev, today):
    os.makedirs("state", exist_ok=True)
    out = {}
    for k, s in songs.items():
        p = prev.get(k, {})
        out[k] = {
            "artist": s["artist"],
            "title": s["title"],
            "channels": sorted(s["channels"]),
            "views": s["views"],
            "first_seen": p.get("first_seen", today),
            "last_seen": today,
        }
    # 사라진 곡도 30일간은 기억해둔다 (재점화 감지용)
    cutoff = (datetime.strptime(today, "%Y-%m-%d") - timedelta(days=30)).strftime("%Y-%m-%d")
    for k, v in prev.items():
        if k not in out and v.get("last_seen", "") >= cutoff:
            out[k] = v
    with open(STATE_PATH, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)


# ---------------------------------------------------------------- 메인

def main():
    key = os.environ.get("YOUTUBE_API_KEY", "").strip()
    if not key:
        log("YOUTUBE_API_KEY 가 없어. GitHub Secrets 확인 필요.")
        sys.exit(1)

    today = datetime.now(KST).strftime("%Y-%m-%d")
    log(f"=== 바이럴 레이더 {today} ===")

    prev, first_run = load_state()
    log(f"이전 상태: {len(prev)}곡 {'(첫 실행)' if first_run else ''}")

    log("1) 유튜브 후보 수집")
    vids, qstats = collect_candidates(key)
    log(f"   → 영상 {len(vids)}건")
    if not vids:
        log("수집 0건.")
        # 아무것도 못 긁었어도 '왜 못 긁었는지'는 리포트로 남긴다.
        # 그냥 끝내버리면 형은 빈 화면만 보고 원인을 알 수 없다.
        diag = {
            "queries": qstats,
            "drops": {},
            "verified": 0,
            "quota_errors": API_ERRORS["quota"],
            "api_errors": API_ERRORS["other"],
        "reasons": dict(API_REASONS),
            "samples": [],
        }
        path = write_report([], today, first_run, 0, 0, diag)
        write_latest(path)
        log(f"완료(빈 결과) → {path}")
        sys.exit(0)

    log("2) 조회수 / 구독자 보강")
    vids = enrich_videos(key, vids)
    subs = enrich_channels(key, vids)

    log("3) 1단 집계 (곡 이름 뽑기)")
    songs1, _ = aggregate(vids, subs)
    log(f"   → 후보 {len(songs1)}곡")

    log("4) 2단 검증 (곡마다 이름으로 재검색)")
    extra, checked = verify_candidates(key, songs1, {v["videoId"] for v in vids}, prev)
    log(f"   → 추가 영상 {len(extra)}건")
    if extra:
        extra = enrich_videos(key, extra)
        subs.update(enrich_channels(key, extra))
        vids = vids + extra

    log("5) Shazam 한국 200 (퇴장 필터)")
    shazam = fetch_shazam_kr()
    log(f"   → {len(shazam)}곡 확보")

    log("6) 최종 집계")
    songs, scan_drops = aggregate(vids, subs)
    log(f"   → {len(songs)}곡")

    log("7) 점수 계산")
    results = score_songs(songs, prev, shazam, today, checked)
    passing = sum(1 for r in results if r.get("passes"))
    log(f"   → 실질 채널 {MIN_CHANNELS}개 이상 {passing}곡")

    log("8) 리포트 작성")
    diag = {
        "queries": qstats,
        "drops": scan_drops,
        "verified": len(extra),
        "quota_errors": API_ERRORS["quota"],
        "api_errors": API_ERRORS["other"],
        "reasons": dict(API_REASONS),
        "samples": [v["title"] for v in vids[:20]],
    }
    path = write_report(results, today, first_run, len(vids), len(songs), diag)
    write_latest(path)
    save_state(songs, prev, today)

    log("9) 메일")
    send_mail(results, today, API_ERRORS["quota"] > 0)
    if API_ERRORS["quota"]:
        log(f"!! 할당량 초과로 검색 {API_ERRORS['quota']}건 거절 — 결과 불완전")
    log(f"완료 → {path}")


if __name__ == "__main__":
    main()
