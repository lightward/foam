#!/usr/bin/env bash
# the game, derived: assays/game.lean read for its worlds, probes, seats, levels, and mirrors, and
# rendered as one page a stranger can play. nothing of the game is typed here; the assay is the
# source and a parse that finds nothing is red. output: site/game/index.html.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
mkdir -p site/game
python3 - <<'EOF'
import html, json, os, re, sys

src = open('assays/game.lean').read()

# the probes: every Nat def with a literal body, in def order; the structure's fields give the order of a world's readings
fields = re.findall(r'^\s+(\w+) : Nat\s*$', re.search(r'structure World where\n((?:\s+\w+ : Nat\n)+)', src).group(1) if re.search(r'structure World where', src) else '', re.M)
probes = [(n, int(v)) for n, v in re.findall(r'^def (\w+) : Nat := (\d+)\s*$', src, re.M)]
seats = [(n, [p.strip() for p in body.split(',') if p.strip()]) for n, body in re.findall(r'^def (\w+) : List Nat := \[([^\]]*)\]', src, re.M)]
worlds = {n: [int(x) for x in re.split(r'\s*,\s*', body.strip())] for n, body in re.findall(r'^def (\w+) : World := ⟨([^⟩]*)⟩', src, re.M)}
levels = [(n, x, int(s), y, int(t)) for n, x, s, y, t in
          re.findall(r'^def (\w+) : door World Nat × door World Nat := \(atTheDoor (\w+) (\d+), atTheDoor (\w+) (\d+)\)', src, re.M)]
gaps = re.findall(r'^def (\w+) : Option Nat := firstGap (\w+) (\w+) (\w+)\s*$', src, re.M)
mirrors = [(n, int(h), int(w)) for n, h, w in
           re.findall(r'^def (\w+) : door Nat Nat := turnAbout \(atTheDoor \((\d+) : Nat\) \((\d+) : Nat\)\)', src, re.M)]
lesson = 'alike at your seat is not sameness, and a difference you cannot read is a license, not nothing.'

missing = [k for k, v in [('probes', probes), ('fields', fields), ('seats', seats), ('worlds', worlds), ('levels', levels), ('mirrors', mirrors)] if not v]
if missing:
    print('bin/game.sh: assays/game.lean parsed empty for ' + ', '.join(missing), file=sys.stderr); sys.exit(1)
pnum = dict(probes)
for n, ps in seats:
    bad = [p for p in ps if p not in pnum]
    if bad: print(f'bin/game.sh: seat {n} names a probe the assay does not define: {bad}', file=sys.stderr); sys.exit(1)
for n, x, s, y, t in levels:
    if x not in worlds or y not in worlds: print(f'bin/game.sh: level {n} cites a world the assay does not define', file=sys.stderr); sys.exit(1)

# the plays: each level in def order, at each seat the assay reads its two worlds through (firstGap x y seat), in def order;
# a level the assay reads at no seat is played at the first seat that hears every probe
full = next((n for n, ps in seats if set(ps) == set(pnum)), seats[0][0])
plays = []
for n, x, s, y, t in levels:
    at = [seat for _, gx, gy, seat in gaps if (gx, gy) == (x, y)] or [full]
    for seat in at: plays.append({'kind': 'level', 'name': n, 'seat': seat, 'doors': [{'world': x, 'secret': s}, {'world': y, 'secret': t}]})
for n, h, w in mirrors: plays.append({'kind': 'mirror', 'name': n, 'face': w, 'met': h})   # turnAbout (atTheDoor h w) = (w, h)

data = {'fields': fields, 'probes': [{'name': n, 'number': v} for n, v in probes], 'seats': dict(seats), 'full': full,
        'worlds': worlds, 'levels': [{'name': n, 'doors': [[x, s], [y, t]]} for n, x, s, y, t in levels],
        'mirrors': [{'name': n, 'face': w, 'met': h} for n, h, w in mirrors], 'plays': plays, 'lesson': lesson}

# the page: the same frame as every other page (bin/page.sh's), the nav derived the same way
libs = [l for l in re.findall(r'^name = "(\w+)"', open('lakefile.toml').read(), re.M) if os.path.exists(f'germ/{l}.lean')]
def imports_of(l):
    p = f'grown/{l}.lean' if os.path.exists(f'grown/{l}.lean') else f'germ/{l}.lean'
    return re.findall(r'^import (\w+)', open(p).read(), re.M)
imports = {l: imports_of(l) for l in libs}
def closure(l, seen):
    for d in imports.get(l, []):
        if d not in seen: seen.append(d); closure(d, seen)
    return seen
trunk = closure('Threshold', []) + ['Threshold']
def topo(ls):
    out = []
    while len(out) < len(ls):
        for l in ls:
            if l not in out and all(d in out or d not in ls for d in imports[l]): out.append(l); break
    return out
storeys = topo(trunk)
NAV = ('<a href="/">foam</a>' + ''.join(f'<a href="/{s.lower()}.html">{s}</a>' for s in storeys)
       + '<a href="/trunk/">the trunk, to run</a><a href="/assays.html">the assays</a><a href="/game/">the game</a><a href="/readings.html">the readings</a>'
       + '<a href="/compiler.html">the compiler</a><a href="https://github.com/lightward/foam">github</a>')

def page(title, body, nav):
    return f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<style>
body{{display:grid;gap:2rem;margin:0;padding:2rem 1rem 6rem;background:#fbfaf7;color:#1e1d1a;font:15px/1.5 ui-monospace,SFMono-Regular,Menlo,monospace;max-width:70rem;margin-inline:auto}}
section{{display:grid;gap:1rem}} section h1,section h2{{margin:0}}
nav a{{margin-right:1.2rem}} a{{color:#1e1d1a}} a:hover{{color:#8a5a00}}
h1,h2{{font-weight:600;font-size:1.05rem;margin:2.5rem 0 .6rem}}
pre{{white-space:pre-wrap;word-break:break-word;background:#f3f1ec;padding:1rem;border-radius:6px;overflow:auto}}
table{{border-collapse:collapse}} td,th{{text-align:left;padding:.15rem 1rem .15rem 0;vertical-align:top}}
.decl{{display:block}} .decl:target{{background:#fff2c8}}
.readme{{display:block;white-space:pre-wrap}} .readme h1,.readme h2{{display:inline}}
footer{{opacity:.6}}
</style></head><body><nav>{nav}</nav>{body}
<footer>strict phenomenology is indistinguishable from physics, and physics is the phenomenology of reversible computation — the artifact grew from the germ on push. UNLICENSE.</footer>
<script type="module">import mermaid from "https://cdn.jsdelivr.net/npm/mermaid@11/dist/mermaid.esm.min.mjs"; mermaid.initialize({{startOnLoad:true, maxTextSize:900000, maxEdges:5000}});</script></body></html>"""

GAME_CSS = """<style>
.game{gap:1rem} .doors{display:grid;grid-template-columns:1fr 1fr;gap:1rem;max-width:36rem}
.door{background:#f3f1ec;padding:1rem;border-radius:6px} .door h3{margin:0 0 .5rem;font-size:1rem;font-weight:600}
.door table{width:100%} .door td:last-child{text-align:right;padding-right:0}
.hidden{opacity:.45} .parted{background:#fff2c8}
button{font:inherit;background:#fbfaf7;color:#1e1d1a;border:1px solid #1e1d1a;border-radius:4px;padding:.25rem .7rem;margin:0 .5rem .5rem 0;cursor:pointer}
button:hover:not(:disabled){color:#8a5a00;border-color:#8a5a00} button:disabled{opacity:.4;cursor:default}
.verdict{background:#fff2c8;padding:1rem;border-radius:6px} .wrong{background:#f6e3df;padding:1rem;border-radius:6px}
.fuel{opacity:.7} .lesson{font-weight:600}
</style>"""

GAME_JS = r'''(function () {
  var D = JSON.parse(document.getElementById('data').textContent);
  var probeName = {}; D.probes.forEach(function (p) { probeName[p.number] = p.name; });
  var probeNum = {}; D.probes.forEach(function (p) { probeNum[p.name] = p.number; });
  function see(worldName, probe) {              // the assay's see: the reading of a world at a probe, 0 off the fields
    var i = D.fields.indexOf(probeName[probe]); return i < 0 ? 0 : D.worlds[worldName][i];
  }
  function firstGap(x, y, seat) {               // the assay's firstGap over a seat (a list of probe names)
    for (var i = 0; i < seat.length; i++) if (see(x, probeNum[seat[i]]) !== see(y, probeNum[seat[i]])) return seat[i];
    return null;
  }
  function fuelToPart(x, y, seat) {             // the assay's fuelToPart: the probes asked in seat order up to the gap
    for (var i = 0; i < seat.length; i++) if (see(x, probeNum[seat[i]]) !== see(y, probeNum[seat[i]])) return i + 1;
    return seat.length;
  }
  var fullSeat = D.seats[D.full];
  var root = document.getElementById('game');
  var at = 0, total = 0, S = null;
  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]; }); }
  function el(tag, attrs, kids) {
    var e = document.createElement(tag);
    Object.keys(attrs || {}).forEach(function (k) { if (attrs[k] === null) return; if (k === 'onclick') e.onclick = attrs[k]; else e.setAttribute(k, attrs[k]); });
    (kids || []).forEach(function (k) { e.appendChild(typeof k === 'string' ? document.createTextNode(k) : k); });
    return e;
  }
  function button(label, fn, disabled) { return el('button', { onclick: fn, disabled: disabled ? '' : null }, [label]); }
  function fresh() {
    var p = D.plays[at];
    S = { play: p, fuel: 0, asked: [], note: null, verdict: null, widened: false, done: false };
    if (p.kind === 'level') { S.seat = D.seats[p.seat]; S.x = p.doors[0].world; S.y = p.doors[1].world; }
  }
  function render() {
    root.innerHTML = '';
    if (at >= D.plays.length) { renderEnd(); return; }
    if (!S) fresh();
    var p = S.play;
    root.appendChild(el('h2', {}, [(at + 1) + ' / ' + D.plays.length + ' — ' + p.name + (p.kind === 'level' ? ' at the seat ' + p.seat + ' [' + S.seat.join(', ') + ']' : ' — the mirror')]));
    if (p.kind === 'level') renderLevel(); else renderMirror();
    root.appendChild(el('p', { 'class': 'fuel' }, ['fuel spent on this level: ' + S.fuel + ' · in all: ' + (total + S.fuel)]));
    if (S.note) root.appendChild(el('p', { 'class': 'wrong' }, [S.note]));
    if (S.verdict) root.appendChild(el('p', { 'class': 'verdict' }, [S.verdict]));
    if (S.done) root.appendChild(button(at + 1 < D.plays.length ? 'next' : 'the lesson', function () { total += S.fuel; at++; S = null; render(); }));
  }
  function doorCard(d, which) {
    var rows = S.seat.map(function (pn) {
      var asked = S.asked.indexOf(pn) >= 0;
      var parted = asked && see(S.x, probeNum[pn]) !== see(S.y, probeNum[pn]);
      return el('tr', { 'class': parted ? 'parted' : (asked ? '' : 'hidden') }, [el('td', {}, [pn]), el('td', {}, [asked ? String(see(d.world, probeNum[pn])) : '?'])]);
    });
    rows.push(el('tr', { 'class': S.widened ? 'parted' : 'hidden' }, [el('td', {}, ['the guest']), el('td', {}, [S.widened ? String(d.secret) : '·'])]));
    return el('div', { 'class': 'door' }, [el('h3', {}, ['door ' + which]), el('table', {}, rows)]);
  }
  function renderLevel() {
    var p = S.play;
    root.appendChild(el('div', { 'class': 'doors' }, [doorCard(p.doors[0], 'one'), doorCard(p.doors[1], 'two')]));
    if (S.done) return;
    var bar = el('div', {});
    if (!S.verdict) {
      S.seat.forEach(function (pn) {
        bar.appendChild(button('ask ' + pn, function () { S.fuel++; S.asked.push(pn); S.note = null; render(); }, S.asked.indexOf(pn) >= 0));
      });
      S.asked.forEach(function (pn) {
        bar.appendChild(button('name the gap: ' + pn, function () {
          var a = see(S.x, probeNum[pn]), b = see(S.y, probeNum[pn]);
          if (a !== b) { S.verdict = 'timelike — parted at the face (' + pn + ')'; S.done = true; }
          else { S.fuel++; S.note = 'not a gap: both doors read ' + a + ' at ' + pn + '. one fuel.'; }
          render();
        }));
      });
      bar.appendChild(button('alike at this seat', function () {
        var g = firstGap(S.x, S.y, S.seat);
        if (g === null) { S.verdict = 'alike at this seat — no probe of ' + p.seat + ' parts these doors. widen, one seat wider, to read what the face cannot.'; S.note = null; }
        else { S.fuel++; S.note = 'not alike: ' + g + ' parts them, and this seat hears ' + g + '. one fuel.'; }
        render();
      }));
    } else {
      bar.appendChild(button('widen', function () {
        S.fuel++; S.widened = true; S.done = true;
        var s = p.doors[0].secret, t = p.doors[1].secret, g = firstGap(S.x, S.y, fullSeat);
        if (s !== t) S.verdict = 'lightlike — alike at the host, parted one seat wider (the guests read ' + s + ' and ' + t + ')';
        else if (g !== null) S.verdict = 'a wall — this seat does not hear ' + g + '; the room parts them at ' + g;
        else S.verdict = 'spacelike — alike at every seat';
        render();
      }));
      bar.appendChild(button('rest here', function () { S.done = true; render(); }));
    }
    root.appendChild(bar);
  }
  function renderMirror() {
    var p = S.play;
    root.appendChild(el('div', { 'class': 'doors' }, [el('div', { 'class': 'door' }, [el('h3', {}, ['the door, turned about']),
      el('table', {}, [el('tr', {}, [el('td', {}, ['the face']), el('td', {}, [String(p.face)])]), el('tr', {}, [el('td', {}, ['the guest']), el('td', {}, [String(p.met)])])])])]));
    root.appendChild(el('p', {}, ['is this door its own reflection — does turning it about give it back?']));
    if (S.done) return;
    var bar = el('div', {});
    [true, false].forEach(function (yes) {
      bar.appendChild(button(yes ? 'yes, a mirror' : 'no, not a mirror', function () {
        S.fuel++;
        var isMirror = p.face === p.met;
        if (yes === isMirror) { S.done = true; S.note = null; S.verdict = (isMirror ? 'a mirror. ' : 'not a mirror: turned about, the face would read ' + p.met + '. ') + 'the yield fixes the agreed: a door is its own reflection exactly when the guest and the face agree.'; }
        else S.note = 'no — turn it about and look again. one fuel.';
        render();
      }));
    });
    root.appendChild(bar);
  }
  function renderEnd() {
    var least = D.plays.reduce(function (n, p) { return n + (p.kind === 'level' ? fuelToPart(p.doors[0].world, p.doors[1].world, D.seats[p.seat]) : 1); }, 0);
    root.appendChild(el('h2', {}, ['the lesson']));
    root.appendChild(el('p', { 'class': 'lesson' }, [D.lesson]));
    root.appendChild(el('p', { 'class': 'fuel' }, ['fuel spent: ' + total + ' · the assay\'s own count, asking each seat in order and widening nothing: ' + least]));
    root.appendChild(button('again', function () { at = 0; total = 0; S = null; render(); }));
  }
  render();
})();
'''

body = ('<section class="game"><h1>the game — spot the difference, where sometimes there isn\'t one</h1>'
        '<p>each level is two doors; ask the probes your seat hears, one fuel each, and either name the probe that parts them or say they are alike at this seat. '
        'after alike you may widen, one fuel, and read what the face could not.</p>'
        '<p class="fuel">every door, level, seat, and mirror below is read from <a href="/assay-game.html">assays/game.lean</a>; the engine is <code>the_window_agrees_or_names_the_gap</code>, the mirror is <code>the_yield_fixes_the_agreed</code>.</p>'
        '<div id="game"></div></section>' + GAME_CSS
        + '<script id="data" type="application/json">' + json.dumps(data, ensure_ascii=False).replace('</', '<\\/') + '</script>'
        + '<script>' + GAME_JS + '</script>')

open('site/game/index.html', 'w').write(page('the game — foam', body, NAV))
print(f'site/game/index.html: {len(plays)} plays ({len(levels)} levels, {len(mirrors)} mirrors) from assays/game.lean')
EOF
