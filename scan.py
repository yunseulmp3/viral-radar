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

# 검색어. 형이 씬 태그를 추가하고 싶으면 여기만 고치면 된다.
# 각 검색은 YouTube 할당량 100유닛. 하루 10,000유닛이니 여유 충분.
QUERIES = [
    "가사 노래",
    "신곡 가사",
    "가사 한국 노래",
    "1시간 반복 노래",
    "가사 힙합 한국",
    "사운드클라우드 한국 랩",
    "언더그라운드 랩 가사",
    "인디 노래 가사",
    "노래 요즘 유행",
    "쇼츠 노래 뭐야",
    "틱톡 유행 노래 한국",
    "가사해석 노래",
]

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
]

# 이 정도 구독자면 대형/기획사 채널로 본다
BIG_CHANNEL_SUBS = 1_000_000
MID_CHANNEL_SUBS = 100_000


# ---------------------------------------------------------------- 유틸

def log(msg):
    print(f"[{datetime.now(KST):%H:%M:%S}] {msg}", flush=True)


def yt(endpoint, key, **params):
    """YouTube Data API 호출. 실패해도 죽지 않고 빈 결과 반환."""
    params["key"] = key
    try:
        r = requests.get(f"{API}/{endpoint}", params=params, timeout=30)
        if r.status_code != 200:
            log(f"  ! {endpoint} HTTP {r.status_code}: {r.text[:200]}")
            return {}
        return r.json()
    except Exception as e:
        log(f"  ! {endpoint} 실패: {e}")
        return {}


# ---------------------------------------------------------------- 제목 정규화

# 제목에서 걷어낼 장식들
BRACKET_RE = re.compile(r"[\[\(\{【（][^\]\)\}】）]*[\]\)\}】）]")
DECOR_RE = re.compile(
    r"(가사\s*(비디오)?|lyrics?|리릭\s*비디오|lyric\s*video|мv|official\s*(audio|video|mv)?"
    r"|audio|visualizer|비주얼라이저|1\s*시간|한시간|1\s*hour|loop|반복|"
    r"slowed(\s*\+?\s*reverb)?|reverb|슬로우(\s*리버브)?|sped\s*up|스페드업|"
    r"nightcore|8d|가사해석|해석|자막|kor\s*sub|번역)",
    re.IGNORECASE,
)
SPACE_RE = re.compile(r"\s+")
SEP_RE = re.compile(r"\s*[-–—|/·:]\s*")


def clean_piece(s):
    s = BRACKET_RE.sub(" ", s)
    s = DECOR_RE.sub(" ", s)
    s = re.sub(r"[\"'“”‘’#♪♬★☆*]+", " ", s)
    s = SPACE_RE.sub(" ", s).strip(" -–—|/·:,.")
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

    parts = SEP_RE.split(t)
    parts = [clean_piece(p) for p in parts]
    parts = [p for p in parts if p and len(p) >= 2]

    if len(parts) < 2:
        return None, None

    artist, title = parts[0], parts[1]

    # 아티스트 자리에 장식만 남은 경우(예: "가사 - 곡명") 걸러냄
    if len(artist) > 40 or len(title) > 60:
        return None, None
    if not artist or not title:
        return None, None

    return artist, title


def _n(s):
    s = (s or "").lower()
    return re.sub(r"[^0-9a-z가-힣ぁ-んァ-ン一-龥]", "", s)


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

def collect_candidates(key):
    """검색어들을 돌면서 최근 업로드 영상 수집."""
    after = (datetime.now(timezone.utc) - timedelta(days=LOOKBACK_DAYS)).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )
    seen = {}
    for q in QUERIES:
        data = yt(
            "search", key,
            part="snippet", q=q, type="video", order="date",
            regionCode="KR", relevanceLanguage="ko",
            publishedAfter=after, maxResults=50,
        )
        items = data.get("items", [])
        log(f"  검색 '{q}' → {len(items)}건")
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
    return list(seen.values())


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


def aggregate(vids, subs):
    """
    1차: 제목 파싱 + 정크/한글 필터
    2차: 아티스트-곡명 순서 교정
    3차: 곡 단위 묶기 (팜 채널 가중 반영)
    """
    # ---- 1차 --------------------------------------------------------
    parsed = []
    for v in vids:
        if is_junk(v["title"]):
            continue
        artist, title = parse_title(v["title"])
        if not artist or not title:
            continue
        # 한글 판정은 '원본 제목' 기준.
        # 파싱된 아티스트/곡명만 보면 'nephillm - ny2mia [가사]' 같은
        # 영문 표기 한국 곡이 통째로 날아간다. 원본에는 '가사'가 남아 있다.
        if REQUIRE_HANGUL and not has_hangul(v["title"]):
            continue
        parsed.append({**v, "artist": artist, "title": title})

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

    # ---- 팜 채널 가중치 ---------------------------------------------
    weights, per_channel = detect_farms(parsed)

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
        s["weighted_channels"] = sum(weights.get(c, 1.0) for c in s["channels"])
        s["farm_channels"] = sum(1 for c in s["channels"] if weights.get(c, 1.0) == 0.0)

    return songs


def score_songs(songs, prev, shazam_keys, today):
    """
    점수 = 채널 증가 모멘텀 × 언더그라운드 가중 × 신선도
    조회수는 보조 지표로만 (로그 스케일).
    """
    results = []
    for k, s in songs.items():
        # 팜 채널을 걷어낸 '실질 채널 수'로 판정한다
        n_ch = s.get("weighted_channels", len(s["channels"]))
        if n_ch < MIN_CHANNELS:
            continue

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
        fresh = 1.0 if days <= 7 else max(0.2, math.exp(-(days - 7) / 14.0))

        on_shazam = k in shazam_keys
        score = momentum * under * fresh
        if on_shazam:
            score *= 0.3   # 퇴장 신호 — 완전 제외는 안 하고 강하게 감점

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


def write_report(results, today, first_run, n_vids, n_songs):
    os.makedirs(REPORT_DIR, exist_ok=True)
    path = f"{REPORT_DIR}/{today}.md"
    top = results[:TOP_N]

    L = []
    L.append(f"# 바이럴 레이더 — {today}")
    L.append("")
    L.append(f"수집 영상 {n_vids}건 · 곡 후보 {n_songs}곡 · 채널 2개 이상 {len(results)}곡")
    L.append("")

    if first_run:
        L.append("> **첫 실행이라 이번 리포트는 기준선(baseline)이야.**")
        L.append("> 모든 곡이 '신규'로 잡히니까 순위는 아직 의미 없어.")
        L.append("> 내일부터 어제 대비 채널 증가가 계산되면서 진짜 순위가 나와.")
        L.append("")

    if not top:
        L.append("_오늘은 조건을 넘은 곡이 없어._")
    else:
        L.append("| # | 곡 | 진입 | 채널 | 어제比 | 조회수 | 최대구독 | Shazam |")
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
            ch_line = f"- 실질 채널 **{r['channels']}개** (어제 대비 +{r['new_channels']})"
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

    L.append("---")
    L.append("")
    L.append("**읽는 법** — 순위는 조회수가 아니라 *서로 다른 채널이 얼마나 빨리 늘고 있나*로 매겨져. "
             "`어제比 +N`이 클수록 지금 불붙는 중. `진입 3일차` 이내 + 채널 급증이 형이 노릴 구간이고, "
             "`Shazam ⚠`가 붙으면 이미 늦은 신호야.")
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
    vids = collect_candidates(key)
    log(f"   → 영상 {len(vids)}건")
    if not vids:
        log("수집 0건. 종료.")
        sys.exit(0)

    log("2) 조회수 / 구독자 보강")
    vids = enrich_videos(key, vids)
    subs = enrich_channels(key, vids)

    log("3) Shazam 한국 200 (퇴장 필터)")
    shazam = fetch_shazam_kr()
    log(f"   → {len(shazam)}곡 확보")

    log("4) 곡 단위 집계")
    songs = aggregate(vids, subs)
    log(f"   → {len(songs)}곡")

    log("5) 점수 계산")
    results = score_songs(songs, prev, shazam, today)
    log(f"   → 채널 {MIN_CHANNELS}개 이상 {len(results)}곡")

    log("6) 리포트 작성")
    path = write_report(results, today, first_run, len(vids), len(songs))
    write_latest(path)
    save_state(songs, prev, today)
    log(f"완료 → {path}")


if __name__ == "__main__":
    main()
