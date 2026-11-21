#!/usr/bin/env python3
"""Independent straightforward reference implementation of rules.md (slow, for cross-checking)."""
import sys, os, re, json, glob, datetime
from collections import defaultdict

data, out = sys.argv[1], sys.argv[2]

def lines_of(path):
    with open(path, 'rb') as f:
        raw = f.read()
    text = raw.decode('utf-8')
    parts = text.split('\n')
    if parts and parts[-1] == '':
        parts.pop()
    return parts[1:]  # drop header

def parse_line(line, n):
    fields = line.split(',')
    if len(fields) != n:
        return None
    res = []
    for f in fields:
        if '"' in f:
            if len(f) >= 2 and f[0] == '"' and f[-1] == '"' and '"' not in f[1:-1]:
                f = f[1:-1]
            else:
                return None
        res.append(f)
    return res

RE_F1 = re.compile(r'([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})Z')
RE_F2 = re.compile(r'([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})([+-])([0-9]{2}):([0-9]{2})')
RE_F3 = re.compile(r'[0-9]+')
EPOCH = datetime.datetime(1970, 1, 1)

def parse_ts(s):
    if RE_F3.fullmatch(s):
        v = int(s)
        if v > 2**63 - 1:
            return None
        return v
    m = RE_F1.fullmatch(s)
    off = 0
    if not m:
        m = RE_F2.fullmatch(s)
        if not m:
            return None
        oh, om = int(m.group(8)), int(m.group(9))
        if oh > 23 or om > 59:
            return None
        off = (oh * 60 + om) * 60000 * (1 if m.group(7) == '+' else -1)
    y, mo, d, h, mi, sec = [int(m.group(i)) for i in range(1, 7)]
    try:
        if y < 1:
            return None
        dt = datetime.datetime(y, mo, d, h, mi, sec)  # validates calendar, hour<24, min<60, sec<60
    except ValueError:
        return None
    return int((dt - EPOCH).total_seconds()) * 1000 - off

man = json.load(open(os.path.join(data, 'manifest.json')))
WS = parse_ts(man['window_start']); WE = parse_ts(man['window_end'])
DAY = 86400000

products = {}
for l in lines_of(os.path.join(data, 'products.csv')):
    f = parse_line(l, 2)
    if f: products[f[0]] = f[1]
campaigns = {}
for l in lines_of(os.path.join(data, 'campaigns.csv')):
    f = parse_line(l, 2)
    if f: campaigns[f[0]] = f[1]

# links
parent = {}
def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x
for p in sorted(glob.glob(os.path.join(data, 'links', '*.csv'))):
    for l in lines_of(p):
        f = parse_line(l, 2)
        if not f or f[0] == '' or f[1] == '':
            continue
        for x in f:
            parent.setdefault(x, x)
        ra, rb = find(f[0]), find(f[1])
        if ra != rb:
            parent[ra] = rb
members = defaultdict(list)
for x in parent:
    members[find(x)].append(x)
name_of = {}
for r, ms in members.items():
    nm = min(ms, key=lambda s: s.encode('utf-8'))
    for x in ms:
        name_of[x] = nm
def person(u):
    return name_of.get(u, u)

# events
copies = defaultdict(list)
for p in sorted(glob.glob(os.path.join(data, 'events', '*.csv'))):
    for l in lines_of(p):
        f = parse_line(l, 7)
        if not f or f[0] == '':
            continue
        copies[f[0]].append(f)
events = []
for eid, cs in copies.items():
    best = min(cs, key=lambda f: parse_ts(f[3]))
    _, uid, ts_s, ing_s, et, pid, price = best
    if uid == '': continue
    ts = parse_ts(ts_s)
    if ts is None or not (WS <= ts < WE): continue
    if et not in ('view', 'cart', 'purchase'): continue
    if pid == '': continue
    pr = 0
    if et == 'purchase':
        if not re.fullmatch(r'[0-9]+', price): continue
        pr = int(price)
        if not (1 <= pr <= 10000000): continue
    ing = parse_ts(ing_s)
    if ing - ts > DAY: continue
    events.append((person(uid), ts, et, pid, pr))

# clicks
clicks_by = defaultdict(dict)
seen = set()
for p in sorted(glob.glob(os.path.join(data, 'clicks', '*.csv'))):
    for l in lines_of(p):
        f = parse_line(l, 4)
        if not f or f[0] == '': continue
        cid, uid, camp, ts_s = f
        if uid == '': continue
        ts = parse_ts(ts_s)
        if ts is None or not (WS - 7 * DAY <= ts < WE): continue
        if camp not in campaigns: continue
        clicks_by[person(uid)][cid] = (ts, cid, camp)

by_person = defaultdict(list)
for e in events:
    by_person[e[0]].append(e)

def day_of(ts): return datetime.date.fromordinal(719163 + ts // DAY)

user_rows = {}
camp_rows = defaultdict(lambda: [0, 0, 0, 0])  # sessions, purch, rev, assisted
for pn, evs in by_person.items():
    evs.sort(key=lambda e: e[1])
    sessions = []
    for e in evs:
        if not sessions or e[1] - sessions[-1][-1][1] > 1800000:
            sessions.append([e])
        else:
            sessions[-1].append(e)
    cl = list(clicks_by.get(pn, {}).values())
    for s in sessions:
        start = s[0][1]
        d = day_of(start)
        row = user_rows.setdefault((pn, d), [0, 0, 0, defaultdict(int)])
        row[0] += 1; row[1] += len(s)
        rev = 0
        for e in s:
            if e[2] == 'purchase':
                rev += e[4]; row[3][products.get(e[3], 'unknown')] += e[4]
        row[2] += rev
        q = [c for c in cl if c[0] <= start and start - c[0] <= 7 * DAY]
        if q:
            mx = max(c[0] for c in q)
            best = min((c for c in q if c[0] == mx), key=lambda c: c[1].encode('utf-8'))
            cid = best[2]
        else:
            cid = 'organic'
        cr = camp_rows[(cid, d)]
        cr[0] += 1; cr[1] += 1 if rev > 0 else 0; cr[2] += rev
        for c in set(c[2] for c in q):
            camp_rows[(c, d)][3] += 1

os.makedirs(out, exist_ok=True)
with open(os.path.join(out, 'user_daily.csv'), 'w') as f:
    f.write('user_id,day,sessions,events,revenue_cents,top_category\n')
    for (pn, d), r in user_rows.items():
        top = ''
        if r[3]:
            mx = max(r[3].values())
            top = min((c for c, v in r[3].items() if v == mx), key=lambda s: s.encode('utf-8'))
        f.write(f'{pn},{d.isoformat()},{r[0]},{r[1]},{r[2]},{top}\n')
with open(os.path.join(out, 'campaign_daily.csv'), 'w') as f:
    f.write('campaign_id,channel,day,sessions,purchasing_sessions,revenue_cents,assisted_sessions\n')
    for (cid, d), r in camp_rows.items():
        ch = 'organic' if cid == 'organic' else campaigns[cid]
        f.write(f'{cid},{ch},{d.isoformat()},{r[0]},{r[1]},{r[2]},{r[3]}\n')
