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

  const here = nodeAt(tree, focus);
  const goals = goalsOf(tree, [], []);
  const total = goals.length;
  const parent = focus.slice(0, -1);
  const last = focus.length ? focus[focus.length - 1] : 0;
  const siblings = focus.length ? kidsOf(nodeAt(tree, parent)).length : 0;

  const button = (label, target, title) =>
    e('button', {
      key: label,
      title,
      disabled: target === null,
      onClick: () => { if (target !== null) setFocus(target); },
      style: { marginRight: '0.4em' }
    }, label);

  const buttons = [
    button('up', focus.length ? parent : null, 'to the node this one is a premise of'),
    button('left', focus.length && last > 0 ? parent.concat([last - 1]) : null,
      'to the premise before this one'),
    button('right', focus.length && last + 1 < siblings ? parent.concat([last + 1]) : null,
      'to the premise after this one'),
    button('top', focus.length ? [] : null, 'to the root')
  ];
  const maxGoals = 12;
  const goalButtons = goals.slice(0, maxGoals).map((g, k) =>
    button('goal ' + k, sameAddr(g, focus) ? null : g, 'to open goal ' + k));

  // One row for a node, then its premises if they are drawn.
  const rows = [];
  const draw = (n, addr) => {
    const kids = kidsOf(n);
    const isFocus = sameAddr(addr, focus);
    const open = countOpen(n);
    const text = (isGoal(n) ? '? ' : '') + n.j + (isGoal(n) ? '' : '   by ' + n.m);
    const note = kids.length && !drawn(addr)
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
  const kidsHere = kidsOf(here).length;
  const premText = isGoal(here) ? 'an open goal'
    : kidsHere === 0 ? 'no premises' : kidsHere === 1 ? '1 premise' : kidsHere + ' premises';
  const goalText = total === 0 ? 'no open goals'
    : countOpen(here) + ' open under the focus, ' + total + ' in all';
  const inFile = sameAddr(focus, props.focus);
  const uri = (props.pos && props.pos.uri) || (envPos && envPos.uri);
  const write = () => {
    if (!uri || !range) return;
    editor.api.applyEdit({ changes: { [uri]: [{ range, newText: motionsText(focus) }] } });
  };

  return e('details', { open: true },
    e('summary', { className: 'mv2 pointer' }, 'Walk: at ' + addrText),
    e('div', { className: 'ml1' },
      e('div', { style: { marginBottom: '0.4em' } }, buttons, goalButtons,
        goals.length > maxGoals
          ? e('span', { style: dimStyle }, '… ' + (goals.length - maxGoals) + ' more goals')
          : null),
      e('div', null, rows),
      e('div', { style: { marginTop: '0.4em' } },
        e('span', null, 'at ' + addrText + ': ' + premText + '; ' + goalText + '.  '),
        inFile
          ? e('span', { style: dimStyle }, 'The #walk in the file is here.')
          : e('span', {
              onClick: write,
              title: 'replace the motions of the #walk by:' + (motionsText(focus) || ' (none)'),
              className: 'link pointer dim',
              style: linkStyle
            }, 'write into the file'))));
}
