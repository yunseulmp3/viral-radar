#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
backtest.py — 과거로 시험하기

핵심 가설:
  "언더 곡이 뜰 때는, 서로 무관한 여러 채널이 짧은 기간에
   같은 곡의 가사/1시간/슬로우 영상을 올린다."

이걸 확인하려고 새 유행을 기다릴 필요가 없다.
이미 터진 곡들의 가사 영상이 유튜브에 그대로 남아 있고,
각 영상에는 업로드 날짜가 붙어 있다.

그걸 날짜순으로 세우면 '채널이 며칠에 걸쳐 몇 개로 늘었는지'
곡선이 그대로 복원된다. 그 곡선을 보고 판단한다:

  - 채널이 실제로 짧은 기간에 급증했나? (가설 성립)
  - 급증했다면 며칠차였나?  (형이 커버를 준비할 시간이 있나)
  - 아니면 처음부터 여러 채널이 흩어져 올렸나? (가설 붕괴)

가설이 틀렸으면 여기서 드러난다. 그게 이 파일의 목적이다.
"""

import os
import re
import sys
import html
from datetime import datetime, timedelta, timezone
from collections import defaultdict

import requests

import scan  # 제목 파싱·정규화·정크 필터는 본체와 똑같은 걸 쓴다

KST = timezone(timedelta(hours=9))

# 검증할 곡. 형이 실제로 덕 봤던 곡들.
# 다른 곡을 시험하고 싶으면 여기에 추가하면 된다.
TARGETS = [
    {"artist": "무소치", "title": "가녀린 손가락에는 사탕 보석 반지 코어"},
    {"artist": "Alfredo", "title": "긍정적 성격을 고쳐라"},
]

# 곡당 몇 건까지 훑을지 (검색 1회 100유닛, 페이지당 50건)
PAGES = 3


def log(m):
    print(f"[{datetime.now(KST):%H:%M:%S}] {m}", flush=True)


def search_all(key, q, pages=PAGES):
    """해당 곡 이름으로 유튜브를 훑는다. 기간 제한 없음 — 과거 전체."""
    out, token = [], None
    for _ in range(pages):
        params = dict(part="snippet", q=q, type="video", order="relevance",
                      maxResults=50, regionCode="KR", relevanceLanguage="ko")
        if token:
            params["pageToken"] = token
        data = scan.yt("search", key, **params)
        items = data.get("items", [])
        out.extend(items)
        token = data.get("nextPageToken")
        if not token or not items:
            break
    return out


def collect_song(key, target):
    """한 곡에 대해 '그 곡의 영상'만 골라내고 (채널, 업로드일) 목록을 만든다."""
    want = scan.norm_key(target["artist"], target["title"])
    q = f"{target['artist']} {target['title']}"
    items = search_all(key, q)

    rows, seen = [], set()
    for it in items:
        vid = (it.get("id") or {}).get("videoId")
        sn = it.get("snippet") or {}
        if not vid or vid in seen:
            continue
        raw = html.unescape(sn.get("title", ""))
        if scan.is_junk(raw):
            continue
        a, t = scan.parse_title(raw)
        if not a or not t:
            continue
        if scan.norm_key(a, t) != want:
            continue
        seen.add(vid)
        pub = (sn.get("publishedAt") or "")[:10]
        if not pub:
            continue
        rows.append({
            "videoId": vid,
            "title": raw,
            "channelId": sn.get("channelId", ""),
            "channelTitle": html.unescape(sn.get("channelTitle", "")),
            "date": pub,
        })
    return rows, len(items)


def build_curve(rows):
    """날짜별 누적 '서로 다른 채널 수' 곡선."""
    by_date = defaultdict(set)
    for r in rows:
        by_date[r["date"]].add(r["channelId"])

    dates = sorted(by_date)
    curve, seen = [], set()
    for d in dates:
        new = by_date[d] - seen
        seen |= by_date[d]
        curve.append({
            "date": d,
            "new_channels": len(new),
            "total_channels": len(seen),
            "new_names": sorted({r["channelTitle"] for r in rows
                                 if r["date"] == d and r["channelId"] in new}),
        })
    return curve


def verdict(curve):
    """가설 판정: 짧은 기간에 채널이 급증한 구간이 있었나."""
    if not curve:
        return "영상을 못 찾음 — 판정 불가", None
    if len(curve) == 1:
        return "업로드가 하루에 몰림 — 시계열 판정 불가", None

    d0 = datetime.strptime(curve[0]["date"], "%Y-%m-%d")
    span = (datetime.strptime(curve[-1]["date"], "%Y-%m-%d") - d0).days
    total = curve[-1]["total_channels"]

    # 7일 창을 밀면서 가장 많이 늘어난 구간 찾기
    best = {"gain": 0, "start": None, "end": None}
    for i, a in enumerate(curve):
        da = datetime.strptime(a["date"], "%Y-%m-%d")
        for b in curve[i:]:
            db = datetime.strptime(b["date"], "%Y-%m-%d")
            if (db - da).days > 7:
                break
            gain = b["total_channels"] - a["total_channels"] + a["new_channels"]
            if gain > best["gain"]:
                best = {"gain": gain, "start": a["date"], "end": b["date"]}

    if best["gain"] >= 3:
        day_n = (datetime.strptime(best["start"], "%Y-%m-%d") - d0).days
        msg = (f"급증 구간 확인 — {best['start']} ~ {best['end']} 사이 "
               f"채널 {best['gain']}개 증가 (최초 업로드로부터 {day_n}일차)")
        return msg, {"gain": best["gain"], "day": day_n,
                     "total": total, "span": span}
    return (f"뚜렷한 급증 없음 — {span}일에 걸쳐 채널 {total}개가 흩어져 올림",
            {"gain": best["gain"], "day": None, "total": total, "span": span})


def main():
    key = os.environ.get("YOUTUBE_API_KEY", "").strip()
    if not key:
        log("YOUTUBE_API_KEY 없음")
        sys.exit(1)

    L = ["# 백테스트 — 과거 바이럴 곡으로 가설 검증", "",
         f"실행 {datetime.now(KST):%Y-%m-%d %H:%M} KST", ""]

    for tg in TARGETS:
        name = f"{tg['artist']} - {tg['title']}"
        log(f"검색: {name}")
        rows, raw_n = collect_song(key, tg)
        log(f"  검색결과 {raw_n}건 중 이 곡으로 확정 {len(rows)}건")

        curve = build_curve(rows)
        msg, stat = verdict(curve)

        L.append(f"## {name}")
        L.append("")
        L.append(f"- 검색 {raw_n}건 → 이 곡의 영상 **{len(rows)}건**")
        L.append(f"- 서로 다른 채널 **{len(set(r['channelId'] for r in rows))}개**")
        L.append(f"- **판정: {msg}**")
        L.append("")

        if curve:
            L.append("| 날짜 | 신규 채널 | 누적 | 올린 채널 |")
            L.append("|------|-----------|------|-----------|")
            for c in curve:
                names = ", ".join(c["new_names"][:4]) or "-"
                L.append(f"| {c['date']} | +{c['new_channels']} | "
                         f"{c['total_channels']} | {names} |")
            L.append("")

        if API_Q():
            L.append("> ⚠ 할당량 초과로 결과가 잘렸을 수 있음")
            L.append("")

    L.append("---")
    L.append("")
    L.append("**읽는 법** — 특정 며칠 사이에 `신규 채널`이 몰려 있으면 "
             "가설대로 '여러 채널이 동시에 붙는' 현상이 실재한 것이고, "
             "그 시점이 최초 업로드로부터 며칠차인지가 형이 확보할 수 있는 "
             "준비 시간이야. 반대로 채널이 몇 달에 걸쳐 하나씩 흩어져 붙었다면 "
             "이 지표로는 유행을 못 잡는다는 뜻이고, 그러면 접근을 바꿔야 해.")
    L.append("")

    os.makedirs("reports", exist_ok=True)
    path = "BACKTEST.md"
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(L))
    log(f"완료 → {path}")


def API_Q():
    return scan.API_ERRORS.get("quota", 0) > 0


if __name__ == "__main__":
    main()
