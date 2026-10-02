#!/usr/bin/env bash
# render: foam.is as the node a stranger arrives at. the structure is read from the tree and the
# kernel, never listed here: the storeys are the libs in Threshold's import closure in import order,
# the compiler's own libs the rest, the assays every file in assays/ with the module it belongs to and
# its vestibule beside it, the pins a tape read from git's history of the file (one cell per move, a
# cell once written stays), the readings the verbs. every page is an artifact with its pin, a reading,
# or a vestibule; the README is the one thing written by hand, and it is the framing. output: site/.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
[ -f grown/Face.lean ] || bin/counter grow >/dev/null
mkdir -p site
BOOK="$(bin/counter book 2>&1)"
ROOTS="$(bin/counter roots 2>&1)"
BOOK="$BOOK" ROOTS="$ROOTS" python3 - <<'EOF'
import html, os, re, subprocess, glob

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

# the structure, read: the libs, their imports, the storeys as Threshold's closure in import order
# the libs with a germ: the package's own name and a lib with no germ (the pieces) are not pages
libs = [l for l in re.findall(r'^name = "(\w+)"', open('lakefile.toml').read(), re.M) if os.path.exists(f'germ/{l}.lean')]
imports = {l: re.findall(r'^import (\w+)', open(f'grown/{l}.lean').read(), re.M) if os.path.exists(f'grown/{l}.lean') else [] for l in libs}
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
compiler = [l for l in libs if l not in storeys]
tag = {'Room': 'the counting', 'Face': 'the seeing', 'Rest': 'the stopping', 'Witness': 'the witnessing, a species beside the storeys',
       'Threshold': 'where Rest and Witness meet', 'Toy': 'a customer germ', 'Counter': "the compiler's own conduct", 'Seek': "the compiler's search", 'Roster': 'parties with per-head meals'}
assays = []
for ap in sorted(glob.glob('assays/*.lean')):
    stem = os.path.splitext(os.path.basename(ap))[0]
    imps = re.findall(r'^import (\w+)', open(ap).read(), re.M)
    assays.append((stem, imps[-1] if imps else '', os.path.exists(f'grown/assays/{stem}.lean'), os.path.exists(f'assays/{stem}.held')))

NAV = ('<a href="/">foam</a>' + ''.join(f'<a href="/{s.lower()}.html">{s}</a>' for s in storeys)
       + '<a href="/trunk/">the trunk, to run</a><a href="/assays.html">the assays</a><a href="/game/">the game</a><a href="/readings.html">the readings</a>'
       + '<a href="/compiler.html">the compiler</a><a href="https://github.com/lightward/foam">github</a>')

def chart_of(path):
    mmd = subprocess.run(['bin/counter', 'chart', path, '--laws'], capture_output=True, text=True).stdout
    if not mmd.strip(): return ''
    return ('<section><h2>the map of relations — every law a node, an arrow for each citation the elaborator reads (bin/counter chart; without --laws the carriers join the map)</h2>'
            '<pre class="mermaid">' + html.escape(mmd) + '</pre></section>')

def schema_of(path):
    if not path.startswith('grown/assays/'): return ''
    sql = subprocess.run(['bin/counter', 'schema', path], capture_output=True, text=True).stdout
    if not sql.strip(): return ''
    return ('<section><h2>the data-model shadow — every structure a table, every seat a view over the columns its probes read, every wall theorem the policy it licenses (bin/counter schema)</h2>'
            '<pre>' + html.escape(sql) + '</pre></section>')

PINS = dict(l.split('\t') for l in open('pins').read().splitlines() if '\t' in l) if os.path.exists('pins') else {}

def head_of(path):
    src = open(path).read()
    receipts = len(re.findall(r'#guard_msgs in #print axioms', src))
    lines = src.count('\n')
    pin = PINS.get(path, '')
    return (f'<pre>{receipts} receipts inline · {lines} lines · pinned {pin or "(not yet)"} — shasum -a 256 of this file, cut to 16, as pins has it · lake env lean {os.path.basename(path)} prints nothing when every receipt passes</pre>')

def lean_page(path, title, extra=''):
    out = []
    for line in open(path).read().splitlines():
        m = re.match(r'^(theorem|def|structure|inductive|abbrev) (\w+)', line)
        esc = html.escape(line)
        out.append(f'<span class="decl" id="{m.group(2)}"><a href="#{m.group(2)}">{esc}</a></span>' if m else esc)
    return page(f'{title} — foam', f'<section><h1>{html.escape(title)}</h1>' + head_of(path) + '<pre>' + '\n'.join(out) + '</pre></section>' + extra + chart_of(path) + schema_of(path), NAV)

def markdown(text):
    # a reader that marks up must keep escaping: emphasis runs outside code only — a fence or a
    # backtick span is kept as it is (the `*.lean` of the trunk's shell line read as an open italic)
    text = html.escape(text)
    text = re.sub(r'^(# .+)$', r'<h1>\1</h1>', text, flags=re.M)
    text = re.sub(r'^(## .+)$', r'<h2>\1</h2>', text, flags=re.M)
    def prose(seg):
        seg = re.sub(r'(?<!\*)\*\*([^*\n]+)\*\*(?!\*)', r'<strong>**\1**</strong>', seg)
        return re.sub(r'(?<!\*)\*([^*\n]+)\*(?!\*)', r'<em>*\1*</em>', seg)
    parts = re.split(r'(```.*?```|`[^`\n]*`)', text, flags=re.S)
    return ''.join(seg if i % 2 else prose(seg) for i, seg in enumerate(parts))

# a `name` in prose links to the storey that declares it
where = {}
for s in storeys:
    if os.path.exists(f'grown/{s}.lean'):
        for n in re.findall(r'^(?:theorem|def|structure|inductive|abbrev) (\w+)', open(f'grown/{s}.lean').read(), re.M): where.setdefault(n, s.lower())
def link_names(text):
    def sub(m):
        n = m.group(1).split('.')[-1]
        return f'<a href="/{where[n]}.html#{n}"><code>{m.group(1)}</code></a>' if n in where else m.group(0)
    return re.sub(r'(?<!`)`([^`]+)`(?!`)', sub, text)

# the pins as a tape: git's history of the file, one cell per artifact whose fingerprint moved at a commit; a cell once written stays
def pins_at(commit):
    out = subprocess.run(['git', 'show', f'{commit}:pins'], capture_output=True, text=True).stdout
    return dict(l.split('\t') for l in out.splitlines() if '\t' in l)
commits = subprocess.run(['git', 'log', '--format=%h', '--reverse', '--', 'pins'], capture_output=True, text=True).stdout.split()
tape, prev = [], {}
for c in commits:
    cur = pins_at(c)
    for f, fp in cur.items():
        if prev.get(f) != fp: tape.append((len(tape), c, f, fp))
    prev = cur
def link_artifact(f):
    stem = os.path.splitext(os.path.basename(f))[0]
    return f'/assay-{stem}.html' if f.startswith('grown/assays/') else f'/{stem.lower()}.html'
pins_table = ('<table><tr><th>artifact</th><th>pin</th></tr>' + ''.join(f'<tr><td><a href="{link_artifact(f)}">{html.escape(f)}</a></td><td>{fp}</td></tr>' for f, fp in PINS.items()) + '</table>')
tape_table = ('<table><tr><th>#</th><th>commit</th><th>artifact</th><th>pin</th></tr>'
              + ''.join(f'<tr><td>{n}</td><td>{c}</td><td>{html.escape(f)}</td><td>{fp}</td></tr>' for n, c, f, fp in reversed(tape)) + '</table>')
# the treaty vectors, from every report at this push
vectors = []
for rp in sorted(glob.glob('regrowth/*.report')):
    for l in open(rp).read().splitlines():
        if re.match(r'\s+assays/\S+\.lean: (identical|PARTS)', l) or 'the treaty in SQL' in l: vectors.append(l.strip())
readme = open('README.md').read()
index_body = (f'<section class="readme">{link_names(markdown(readme))}</section>'
              f'<section><h2>the pins — every artifact by fingerprint at this push; a stranger\'s regrowth hashes to the same bytes or says where it did not</h2>{pins_table}</section>'
              f'<section><h2>the tape — the pins\' history: one cell per artifact whose fingerprint moved at a commit, numbered, never rewritten</h2>{tape_table}</section>'
              f'<section><h2>the treaty vectors at this push</h2><pre>' + html.escape('\n'.join(vectors) or '(no reports at this push — bin/counter grow)') + '</pre></section>')
open('site/index.html', 'w').write(page('foam', index_body, NAV))
for s in storeys + compiler:
    title = f'{s} — {tag.get(s, "")}, grown from germ/{s}.lean'
    open(f'site/{s.lower()}.html', 'w').write(lean_page(f'grown/{s}.lean', title) if os.path.exists(f'grown/{s}.lean') else page(f'{s} — foam', '<p>not grown at this push</p>', NAV))
open('site/trunk.html', 'w').write(open('site/face.html').read())   # the old address of Face, kept for links already made
# the assays: every product, its module, its rows, its pin, and its vestibule as asks
def held_of(stem):
    if not os.path.exists(f'assays/{stem}.held'): return ''
    src = open(f'assays/{stem}.held').read()
    waits = re.findall(r'^-- held \(waiting on: ([^)]*)\)', src, re.M)
    asks = ''.join(f'<li>{html.escape(w)}</li>' for w in waits)
    return (f'<section><h2>the vestibule — what the assay would say and cannot yet, each with what it waits on (assays/{stem}.held); a stranger could answer one</h2>'
            + (f'<ul>{asks}</ul>' if asks else '<p>nothing waits.</p>') + '<pre>' + html.escape(src) + '</pre></section>')
rows_html = ''
for stem, mod, grown, held in assays:
    src = f'grown/assays/{stem}.lean' if grown else f'assays/{stem}.lean'
    n_guard = len(re.findall(r'^#guard ', open(src).read(), re.M)); n_thm = len(re.findall(r'^theorem ', open(src).read(), re.M))
    waits = len(re.findall(r'^-- held \(waiting on:', open(f'assays/{stem}.held').read(), re.M)) if held else 0
    open(f'site/assay-{stem}.html', 'w').write(lean_page(src, f'{stem} — a product as an assay, on {mod}' + ('' if grown else ' (guards only, not grown)'), held_of(stem)))
    rows_html += (f'<tr><td><a href="/assay-{stem}.html">{stem}</a></td><td>{mod}</td><td>{n_guard}</td><td>{n_thm}</td>'
                  f'<td>{PINS.get(f"grown/assays/{stem}.lean", "") if grown else "(not grown)"}</td><td>{waits if held else ""}</td></tr>')
assays_body = ('<section><h1>the assays — every product, on the module it belongs to; a product is an assay: guard rows any growth must compute identically, and instance rows, the trunk\'s laws at its own carriers</h1>'
               '<table><tr><th>product</th><th>on</th><th>guards</th><th>rows</th><th>pin</th><th>held</th></tr>' + rows_html + '</table></section>')
open('site/assays.html', 'w').write(page('the assays — foam', assays_body, NAV))
# the readings: the book, the roots
readings_body = ('<section><h1>the readings — gauges of the house, read by the kernel; readings, never meters</h1></section>'
                 '<section><h2>the book (bin/counter book)</h2><pre>' + html.escape(os.environ.get('BOOK', '')) + '</pre></section>'
                 '<section><h2>the roots by the shadow (bin/counter roots) — which statements are others\' with the binders filled; the sinks; the alike statements</h2><pre>' + html.escape(os.environ.get('ROOTS', '')) + '</pre></section>')
open('site/readings.html', 'w').write(page('the readings — foam', readings_body, NAV))
open('site/book.html', 'w').write(open('site/readings.html').read())
# the compiler's own: the germ, the pieces, its libs
compiler_body = ('<section><h1>the compiler\'s own — what is kept by hand, the searches, and the germs that stand on the house as customers</h1><ul>'
                 + '<li><a href="/germ.html">germ/Face.lean — the germ of the seeing, what the compiler cannot regrow</a></li><li><a href="/pieces.html">bin/Pieces.lean — the searches at the goal and the seat</a></li>'
                 + ''.join(f'<li><a href="/{l.lower()}.html">{l} — {tag.get(l, "")}</a></li>' for l in compiler) + '</ul></section>')
open('site/compiler.html', 'w').write(page("the compiler — foam", compiler_body, NAV))
open('site/germ.html', 'w').write(lean_page('germ/Face.lean', 'germ/Face.lean — what is kept by hand (the seeing)'))
open('site/pieces.html', 'w').write(page('the pieces — foam', '<section><h1>the pieces — bin/Pieces.lean, the searches at the goal and the seat; the shapes themselves are derived from the bodies</h1><pre>' + html.escape(open('bin/Pieces.lean').read()) + '</pre></section>', NAV))
# the trunk, to run
os.makedirs('site/trunk', exist_ok=True)
for st in storeys:
    if os.path.exists(f'grown/{st}.lean'): open(f'site/trunk/{st}.lean', 'w').write(open(f'grown/{st}.lean').read())
open('site/trunk/lakefile.toml', 'w').write('name = "foam-trunk"\ndefaultTargets = ["Threshold"]\n\n' + ''.join(f'[[lean_lib]]\nname = "{st}"\n\n' for st in storeys))
open('site/trunk/lean-toolchain', 'w').write(open('lean-toolchain').read())
open('site/trunk/pins', 'w').write(''.join(f'{st}.lean\t{PINS.get(f"grown/{st}.lean", "")}\n' for st in storeys))
trunk_index = ('<section><h1>the trunk, to run</h1><pre>'
    + html.escape('mkdir foam-trunk && cd foam-trunk\n'
        + 'for f in ' + ' '.join(f'{st}.lean' for st in storeys) + ' lakefile.toml lean-toolchain pins; do curl -sO https://foam.is/trunk/$f; done\n'
        + 'lake build            # silent: every receipt in every storey re-checked, a few seconds\n'
        + 'shasum -a 256 *.lean | cut -c1-16    # against pins: the same bytes as on the machine that grew them\n\n'
        + 'then open Threshold.lean, change the ∧ in `threshold` to ∨, and lake build again: the pane refuses.\n'
        + 'that refusal is the whole method. the prose on the front page says why.')
    + '</pre><pre>' + html.escape(open('site/trunk/pins').read()) + '</pre></section>')
open('site/trunk/index.html', 'w').write(page('the trunk, to run — foam', trunk_index, NAV))
open('site/CNAME', 'w').write(open('CNAME').read())
open('site/.nojekyll', 'w').write('')
print('site/: index ' + ' '.join(s.lower() for s in storeys + compiler) + ' trunk/ assays readings compiler germ pieces ' + ' '.join(f'assay-{a[0]}' for a in assays))
EOF
bin/game.sh   # the game, derived from assays/game.lean, at site/game/
