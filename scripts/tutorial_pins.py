#!/usr/bin/env python3
"""Tie the statements a tutorial displays to the Lean declarations they cite.

    python3 -I scripts/tutorial_pins.py write <tutorial.md>
    python3 -I scripts/tutorial_pins.py check <tutorial.md>

A tutorial in Markdown cites Lean in three ways, each marked so this script
can find it.

* An EXACT pin.  An HTML comment naming one or more declarations, then a
  blank line, then an indented block, then a caption line:

      <!-- lean: GLS.completeness -->

          theorem GLS.completeness : Completeness
            where GLS.Completeness :=
              ∀ (s : GLS.Seq), Valid s → Nonempty (Fam s)

      *Lean:* [`GLS.completeness`](permalink) · PROVED · axioms: `Quot.sound`, `propext`

  The block and the caption are written by `write`, from `#statement` and
  `#statement_location` (ProofTools/Audit/Statement.lean): the statement
  shown is printed by Lean, never typed.  GitHub does not display the
  comment.

* A PARAPHRASE pin: the same comment ending in `paraphrase`.  The block
  under it is the author's, in conventional notation; only the caption is
  written, and it says "in paraphrase".

* An inline mention: write [`exchange`](lean:GLS.exchange).  `write`
  turns it into an ordinary link to the declaration's source lines, with
  the full name kept as the link's title, so that it renders anywhere and
  can still be found.

`write` also generates the pins module named in the page's header comment,

    <!-- lean-pins: module GLS.TutorialPins; import GLS; open GLS -->

in which every pin is a `#guard_msgs` test whose expected output is exactly
what the page shows, and every mention must resolve.  The module is part of
the library, so `lake build` fails when the page and the library disagree.

`check` regenerates that module from the page alone and fails if the file
on disk differs (the page was edited and `write` not run), then builds it.

Status is never typed: PROVED or OPEN, and the axioms, come from
`collectAxioms`.  The prose around a pin is not checked, and the page
should say so.

Written 2026-11-26.  Core Python only.
"""
import os
import re
import subprocess
import sys

PIN = re.compile(r'^<!-- lean: (.+?) -->\s*$')
HEADER = re.compile(r'^<!-- lean-pins: (.+?) -->\s*$')
CAPTION = re.compile(r'^\*Lean(, in paraphrase)?:\* ')
MENTION = re.compile(
    r'\[([^\]]+)\]\((?:lean:([\w.\'₀-₉]+)|(https://github\.com/[^ )]+) "([\w.\'₀-₉]+)")\)')
CAP_ITEM = re.compile(
    r'\[`([\w.\'₀-₉]+)`\]\([^)]*\) · (PROVED|OPEN) · axioms: ([^;]*)')
MARK = '@@@PIN@@@'


def die(msg):
    print('tutorial_pins: ' + msg, file=sys.stderr)
    sys.exit(1)


def sh(args, cwd):
    return subprocess.run(args, cwd=cwd, capture_output=True, text=True)


# ---------------------------------------------------------------- the page

def parse_header(lines):
    for ln in lines:
        m = HEADER.match(ln)
        if m:
            cfg = {'import': [], 'open': []}
            for part in m.group(1).split(';'):
                k, _, v = part.strip().partition(' ')
                if k == 'module':
                    cfg['module'] = v.strip()
                elif k in ('import', 'open'):
                    cfg[k] += v.split()
            if 'module' not in cfg:
                die('the lean-pins header names no module')
            return cfg
    die('no <!-- lean-pins: ... --> header in the page')


def find_pins(lines):
    """Each pin: names, paraphrase?, the line span of its block, and the
    index of its caption line (or None)."""
    pins = []
    i = 0
    while i < len(lines):
        m = PIN.match(lines[i])
        if not m:
            i += 1
            continue
        words = m.group(1).split()
        para = words[-1] == 'paraphrase'
        names = words[:-1] if para else words
        j = i + 1
        while j < len(lines) and lines[j].strip() == '':
            j += 1
        b0 = j
        while j < len(lines) and (lines[j].startswith('    ') or lines[j].strip() == ''):
            j += 1
        b1 = j
        while b1 > b0 and lines[b1 - 1].strip() == '':
            b1 -= 1
        k = b1
        while k < len(lines) and lines[k].strip() == '':
            k += 1
        cap = k if k < len(lines) and CAPTION.match(lines[k]) else None
        pins.append({'at': i, 'names': names, 'para': para,
                     'block': (b0, b1), 'caption': cap})
        i = (cap + 1) if cap is not None else b1
    return pins


def mentions(text):
    out = []
    for m in MENTION.finditer(text):
        out.append(m.group(2) or m.group(4))
    return out


# ---------------------------------------------------------------- Lean

def project_dir(md_path):
    d = os.path.dirname(os.path.abspath(md_path))
    while d != '/':
        if os.path.exists(os.path.join(d, 'lakefile.toml')) or \
           os.path.exists(os.path.join(d, 'lakefile.lean')):
            return d
        d = os.path.dirname(d)
    die('no lakefile above ' + md_path)


def preamble(cfg):
    out = [f'import {m}' for m in cfg['import']]
    out.append('import ProofTools.Audit.Statement')
    out.append('')
    if cfg['open']:
        out.append('open ' + ' '.join(cfg['open']))
    out.append('set_option pp.funBinderTypes true')
    return out


def query(cfg, proj, names):
    """For each name: the lines of `#statement` without the status line,
    the status line, and the declaring module and lines."""
    src = preamble(cfg)
    for n in names:
        src += [f'#eval IO.println "{MARK} {n}"', f'#statement {n}',
                f'#statement_location {n}']
    tmp = os.path.join(proj, '.lake', 'tutorial_pins_query.lean')
    os.makedirs(os.path.dirname(tmp), exist_ok=True)
    with open(tmp, 'w') as f:
        f.write('\n'.join(src) + '\n')
    r = sh(['lake', 'env', 'lean', tmp], proj)
    os.remove(tmp)
    if r.returncode != 0:
        errs = [ln.split('error', 1)[-1] for ln in (r.stdout + r.stderr).split('\n')
                if 'error' in ln]
        die('Lean failed on the query:\n  ' + '\n  '.join(errs))
    res = {}
    for chunk in r.stdout.split(MARK + ' ')[1:]:
        head, _, body = chunk.partition('\n')
        out = body.rstrip('\n').split('\n')
        mod, l0, l1 = out[-1].split()
        status = out[-2]
        res[head.strip()] = {'sig': out[:-2], 'status': status,
                             'module': mod, 'lines': (int(l0), int(l1))}
    missing = [n for n in names if n not in res]
    if missing:
        die('no answer from Lean for ' + ', '.join(missing))
    return res


def source_path(proj, repo, module):
    rel = module.replace('.', '/') + '.lean'
    for base in (proj, repo):
        p = os.path.join(base, rel)
        if os.path.exists(p):
            return os.path.relpath(p, repo)
    die('no source file for module ' + module)


def repo_info(proj):
    root = sh(['git', 'rev-parse', '--show-toplevel'], proj).stdout.strip()
    url = sh(['git', 'remote', 'get-url', 'origin'], proj).stdout.strip()
    m = re.search(r'github\.com[:/](.+?)(?:\.git)?$', url)
    if not m:
        die('origin is not a GitHub remote: ' + url)
    sha = sh(['git', 'rev-parse', '--short', 'HEAD'], proj).stdout.strip()
    return root, 'https://github.com/' + m.group(1), sha


# ---------------------------------------------------------------- writing

def status_md(status):
    """`PROVED · axioms: a, b` as the caption shows it."""
    word, _, axs = status.partition(' · axioms: ')
    shown = 'none' if axs == 'none' else ', '.join(f'`{a}`' for a in axs.split(', '))
    return f'{word} · axioms: {shown}'


def caption(names, para, info, link):
    items = [f'[`{n}`]({link(n)}) · {status_md(info[n]["status"])}' for n in names]
    return ('*Lean, in paraphrase:* ' if para else '*Lean:* ') + '; '.join(items)


def write(md_path):
    proj = project_dir(md_path)
    lines = open(md_path, encoding='utf-8').read().split('\n')
    cfg = parse_header(lines)
    pins = find_pins(lines)
    text = '\n'.join(lines)
    names = sorted({n for p in pins for n in p['names']} | set(mentions(text)))
    info = query(cfg, proj, names)
    repo, base, sha = repo_info(proj)
    dirty = set()

    def link(n):
        path = source_path(proj, repo, info[n]['module'])
        if sh(['git', 'diff', '--quiet', 'HEAD', '--', path], repo).returncode != 0:
            dirty.add(path)
        l0, l1 = info[n]['lines']
        return f'{base}/blob/{sha}/{path}#L{l0}-L{l1}'

    # Rewrite from the bottom up, so that earlier line numbers stay valid.
    for p in sorted(pins, key=lambda p: -p['at']):
        b0, b1 = p['block']
        end = (p['caption'] + 1) if p['caption'] is not None else b1
        if p['para']:
            block = lines[b0:b1]
        else:
            block = []
            for k, n in enumerate(p['names']):
                if k:
                    block.append('')
                block += ['    ' + s if s else '' for s in info[n]['sig']]
        lines[b0:end] = block + ['', caption(p['names'], p['para'], info, link)]

    text = '\n'.join(lines)
    text = MENTION.sub(
        lambda m: f'[{m.group(1)}]({link(m.group(2) or m.group(4))} '
                  f'"{m.group(2) or m.group(4)}")', text)
    with open(md_path, 'w', encoding='utf-8') as f:
        f.write(text)
    write_module(md_path, proj, cfg)
    if dirty:
        print('tutorial_pins: these files differ from HEAD, so their links '
              'may point at the wrong lines; commit them and run write '
              'again:\n  ' + '\n  '.join(sorted(dirty)))
    print(f'tutorial_pins: {len(pins)} pins, {len(mentions(text))} mentions, '
          f'links at {sha}')


# ---------------------------------------------------------------- the module

def module_text(md_path, cfg):
    lines = open(md_path, encoding='utf-8').read().split('\n')
    pins = find_pins(lines)
    out = ['/-',
           f'Generated by `scripts/tutorial_pins.py` from `{os.path.basename(md_path)}`.',
           'Do not edit: run the script.  Each test below expects exactly what',
           'the page shows; the build fails when the page and the library differ.',
           '-/']
    out += preamble(cfg)
    out.append('')
    for p in pins:
        if p['caption'] is None:
            die(f'the pin at line {p["at"] + 1} has no caption: run write')
        cap = lines[p['caption']]
        status = {m.group(1): f'{m.group(2)} · axioms: {m.group(3).replace("`", "")}'
                  for m in CAP_ITEM.finditer(cap)}
        if set(status) != set(p['names']):
            die(f'the caption at line {p["caption"] + 1} does not match its pin')
        if p['para']:
            for n in p['names']:
                out += [f'/-- info: {status[n]} -/',
                        f'#guard_msgs in #statement_status {n}', '']
            continue
        b0, b1 = p['block']
        block = [s[4:] if s.startswith('    ') else s for s in lines[b0:b1]]
        groups, cur = [], []
        for s in block:
            if s == '' and cur:
                groups.append(cur)
                cur = []
            elif s != '':
                cur.append(s)
        if cur:
            groups.append(cur)
        if len(groups) != len(p['names']):
            die(f'the block at line {b0 + 1} does not have one statement per name')
        for n, g in zip(p['names'], groups):
            out += ['/--', 'info: ' + g[0]] + g[1:] + [status[n], '-/',
                    f'#guard_msgs in #statement {n}', '']
    seen = set()
    for n in mentions('\n'.join(lines)):
        if n not in seen:
            seen.add(n)
            out.append(f'#guard_msgs (drop info) in #statement_location {n}')
    return '\n'.join(out) + '\n'


def module_path(proj, cfg):
    return os.path.join(proj, cfg['module'].replace('.', '/') + '.lean')


def write_module(md_path, proj, cfg):
    with open(module_path(proj, cfg), 'w', encoding='utf-8') as f:
        f.write(module_text(md_path, cfg))


def check(md_path):
    proj = project_dir(md_path)
    lines = open(md_path, encoding='utf-8').read().split('\n')
    cfg = parse_header(lines)
    path = module_path(proj, cfg)
    want = module_text(md_path, cfg)
    have = open(path, encoding='utf-8').read() if os.path.exists(path) else ''
    if want != have:
        die(f'{os.path.relpath(path, proj)} is stale: run write')
    r = sh(['lake', 'build', cfg['module']], proj)
    if r.returncode != 0:
        die('the pins do not hold:\n' + r.stdout[-4000:] + r.stderr[-2000:])
    print(f'tutorial_pins: {len(find_pins(lines))} pins hold')


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ('write', 'check'):
        die('usage: tutorial_pins.py write|check <tutorial.md>')
    (write if sys.argv[1] == 'write' else check)(sys.argv[2])
