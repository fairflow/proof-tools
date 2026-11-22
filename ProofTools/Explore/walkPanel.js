// The panel of `#walk` (ProofTools.Explore.Panel): an attempt drawn as a tree
// in the infoview, with nodes to click.  A trial; `set_option walk.panel true`.
//
// Props, from Lean:
//   tree    a node: { j: text of the judgment, m: text of the move (absent at
//           an open goal), kids: the premises, as nodes }
//   focus   the address the motions of the `#walk` reach: premise numbers
//           from the root
//   range   where the motions are written in the file (an LSP range)
// and, from the infoview, `pos` (the document and the editor's position).
//
// The focus is kept in the panel: a click moves it and writes nothing.
// "write into the file" replaces the motions of the `#walk` by the path to
// the focus; then the file's walk and the panel agree again.
//
// What the panel says at a focus is what the view of `#walk` says there
// (`Walk.lean`), by the same rules, written again here:
//   the buttons     the motions that can be made, in the order they are
//                   offered: `Cursor.motions` (`motionsAt`)
//   the rows        from the root to the focus, and the premises of the
//                   focus, numbered and with `[closed]` or `[n open]`:
//                   the lines of `Cursor.view`
//   the last line   `Cursor.viewFoot` (`footAt`)
// A change to one of those in Lean is to be made here too.
import * as React from 'react';
import { EditorContext, EnvPosContext } from '@leanprover/infoview';

const e = React.createElement;

const isGoal = n => n.m === undefined || n.m === null;
const kidsOf = n => n.kids || [];
const key = a => a.join('.');
const isPrefix = (a, b) => a.length <= b.length && a.every((x, i) => x === b[i]);
const sameAddr = (a, b) => a.length === b.length && isPrefix(a, b);

/** The number of open goals under a node. */
function countOpen(n) {
  return isGoal(n) ? 1 : kidsOf(n).reduce((s, k) => s + countOpen(k), 0);
}

/** The node at an address, or undefined. */
function nodeAt(tree, addr) {
  let n = tree;
  for (const i of addr) {
    if (!n) return undefined;
    n = kidsOf(n)[i];
  }
  return n;
}

/** The addresses of the open goals, leftmost first. */
function goalsOf(n, addr, out) {
  if (isGoal(n)) out.push(addr);
  else kidsOf(n).forEach((k, i) => goalsOf(k, addr.concat([i]), out));
  return out;
}

/** The motions that reach an address from the root, as `#walk` reads them. */
function motionsText(addr) {
  return addr.map(i => ' down ' + i).join('');
}

/** Is the open goal at `g` left of the address `f`: before it, and not under it. */
function leftOf(g, f) {
  for (let i = 0; i < g.length && i < f.length; i++) {
    if (g[i] !== f[i]) return g[i] < f[i];
  }
  return false;
}

/** The motions that can be made from an address, in the order `#walk` offers
 * them (`Cursor.motions`), each as it is written and with the address it
 * reaches: `down i` for each premise; `up`, `left`, `right`; `top`, unless at
 * the root; `goal k` for each open goal, unless the focus is that goal. */
export function motionsAt(tree, focus) {
  const out = [];
  kidsOf(nodeAt(tree, focus)).forEach((_, i) =>
    out.push({ text: 'down ' + i, to: focus.concat([i]), title: 'to premise ' + i + ' of the focus' }));
  if (focus.length) {
    const parent = focus.slice(0, -1);
    const last = focus[focus.length - 1];
    const siblings = kidsOf(nodeAt(tree, parent)).length;
    out.push({ text: 'up', to: parent, title: 'to the node this one is a premise of' });
    if (last > 0) {
      out.push({ text: 'left', to: parent.concat([last - 1]), title: 'to the premise before this one' });
    }
    if (last + 1 < siblings) {
      out.push({ text: 'right', to: parent.concat([last + 1]), title: 'to the premise after this one' });
    }
    out.push({ text: 'top', to: [], title: 'to the root' });
  }
  goalsOf(tree, [], []).forEach((g, k) => {
    if (!sameAddr(g, focus)) out.push({ text: 'goal ' + k, to: g, title: 'to open goal ' + k });
  });
  return out;
}

/** The last line of the view at an address (`Cursor.viewFoot`): the address,
 * and where the open goals are. */
export function footAt(tree, focus) {
  const addr = focus.length ? focus.join('.') : 'the root';
  const node = nodeAt(tree, focus);
  const goals = goalsOf(tree, [], []);
  const total = goals.length;
  const left = goals.filter(g => leftOf(g, focus)).length;
  if (isGoal(node)) return 'at ' + addr + ': open goal ' + left + '; ' + total + ' open in all';
  const n = kidsOf(node).length;
  const prem = n === 0 ? 'no premises' : n === 1 ? '1 premise' : n + ' premises';
  const where = total === 0 ? 'no open goals'
    : 'open goals: ' + countOpen(node) + ' under the focus, ' + left + ' left of it, ' + total + ' in all';
  return 'at ' + addr + ': ' + prem + '; ' + where;
}

/** As many motions are offered as `#walk` offers under Messages (`maxOffered`). */
const maxOffered = 40;

const linkStyle = { color: 'var(--vscode-textLink-foreground)' };
const dimStyle = { opacity: 0.6 };

export default function WalkPanel(props) {
  const tree = props.tree;
  const range = props.range;
  const editor = React.useContext(EditorContext);
  const envPos = React.useContext(EnvPosContext);
  // The walk as the file has it.  When it changes, the panel follows it.
  const stamp = JSON.stringify([props.focus, range]);
  const [kept, setKept] = React.useState({ stamp, focus: props.focus, opened: {} });
  const st = kept.stamp === stamp ? kept : { stamp, focus: props.focus, opened: {} };
  const focus = nodeAt(tree, st.focus) ? st.focus : [];
  // To move the focus: what was closed by hand on the way to it is drawn again.
  const setFocus = f => {
    const opened = Object.assign({}, st.opened);
    for (let i = 0; i <= f.length; i++) {
      const k = key(f.slice(0, i));
      if (opened[k] === false) delete opened[k];
    }
    setKept({ stamp, focus: f, opened });
  };

  // The premises of a node are drawn if it is on the way to the focus, or is
  // the focus, unless it was opened or closed by hand.
  const drawn = a => (key(a) in st.opened ? st.opened[key(a)] : isPrefix(a, focus));
  const toggle = a => {
    const opened = Object.assign({}, st.opened);
    opened[key(a)] = !drawn(a);
    setKept({ stamp, focus, opened });
  };

  // The buttons: the motions that can be made from the focus.
  const motions = motionsAt(tree, focus);
  const buttons = motions.slice(0, maxOffered).map(m =>
    e('button', {
      key: m.text,
      title: m.title,
      onClick: () => setFocus(m.to),
      style: { marginRight: '0.4em' }
    }, m.text));

  // One row for a node, then its premises if they are drawn.
  const rows = [];
  const draw = (n, addr) => {
    const kids = kidsOf(n);
    const isFocus = sameAddr(addr, focus);
    // A premise of the focus has its number, as `down i` reads it.
    const isPremise = addr.length === focus.length + 1 && isPrefix(focus, addr);
    const open = countOpen(n);
    const text = (isPremise ? addr[addr.length - 1] + ': ' : '') +
      (isGoal(n) ? '? ' : '') + n.j + (isGoal(n) ? '' : '   by ' + n.m);
    // Whether a node is closed: said of the premises of the focus, as the
    // view says it, and of any node whose premises are not drawn.
    const note = !isGoal(n) && (isPremise || (kids.length && !drawn(addr)))
      ? (open === 0 ? '   [closed]' : '   [' + open + ' open]') : '';
    rows.push(e('div', {
      key: key(addr) || 'root',
      style: {
        paddingLeft: (addr.length * 1.2) + 'em',
        whiteSpace: 'pre-wrap',
        background: isFocus ? 'var(--vscode-editor-selectionBackground)' : undefined
      }
    },
      e('span', {
        onClick: kids.length ? () => toggle(addr) : undefined,
        title: kids.length ? (drawn(addr) ? 'hide its premises' : 'show its premises') : undefined,
        className: kids.length ? 'pointer' : undefined,
        style: { display: 'inline-block', width: '1.2em' }
      }, kids.length ? (drawn(addr) ? '▾' : '▸') : ''),
      e('span', {
        onClick: () => setFocus(addr),
        title: 'put the focus here',
        className: 'pointer font-code',
        style: { fontWeight: isFocus ? 'bold' : undefined }
      }, text),
      note ? e('span', { style: dimStyle, className: 'font-code' }, note) : null));
    if (drawn(addr)) kids.forEach((k, i) => draw(k, addr.concat([i])));
  };
  draw(tree, []);

  const addrText = focus.length ? focus.join('.') : 'the root';
  const inFile = sameAddr(focus, props.focus);
  const uri = (props.pos && props.pos.uri) || (envPos && envPos.uri);
  const write = () => {
    if (!uri || !range) return;
    editor.api.applyEdit({ changes: { [uri]: [{ range, newText: motionsText(focus) }] } });
  };

  return e('details', { open: true },
    e('summary', { className: 'mv2 pointer' }, 'Walk: at ' + addrText),
    e('div', { className: 'ml1' },
      e('div', { style: { marginBottom: '0.4em' } }, buttons,
        motions.length > maxOffered
          ? e('span', { style: dimStyle }, '… and ' + (motions.length - maxOffered) + ' more')
          : null),
      e('div', null, rows),
      e('div', { style: { marginTop: '0.4em' } },
        e('span', null, footAt(tree, focus) + '.  '),
        inFile
          ? e('span', { style: dimStyle }, 'The #walk in the file is here.')
          : e('span', {
              onClick: write,
              title: 'replace the motions of the #walk by:' + (motionsText(focus) || ' (none)'),
              className: 'link pointer dim',
              style: linkStyle
            }, 'write into the file'))));
}
