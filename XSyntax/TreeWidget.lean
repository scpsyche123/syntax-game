import Lean
import Lean.Widget.UserWidget

namespace XSyntax

@[widget_module]
def xTreeGrowthWidget : Lean.Widget.Module where
  javascript := "
import * as React from 'react';

function textOf(x) {
  if (x == null) return '';
  if (typeof x === 'string') return x;
  if (Array.isArray(x)) return x.map(textOf).join('');
  if (typeof x === 'object') {
    if (typeof x.text === 'string') return x.text;
    if (typeof x.content === 'string') return x.content;
    if (x.contents != null) return textOf(x.contents);
    if (x.children != null) return textOf(x.children);
    if (x.val != null) return textOf(x.val);
    return Object.values(x).map(textOf).join('');
  }
  return String(x);
}

function parseGoal(goal) {
  const raw = textOf(goal?.type);
  const labelMatch = raw.match(/([A-Za-z]+(?:P|′|⁰))/);
  const targetMatch = raw.match(/\"([^\"]*)\"/);
  return {
    label: labelMatch ? labelMatch[1] : 'CP',
    target: targetMatch ? targetMatch[1] : ''
  };
}

function base(label) {
  return label.replace(/P$|′$|⁰$/u, '');
}

function isXP(label) { return label.endsWith('P'); }
function isBar(label) { return label.endsWith('′'); }
function isZero(label) { return label.endsWith('⁰'); }
function barOf(label) { return base(label) + '′'; }
function zeroOf(label) { return base(label) + '⁰'; }

let nextId = 1;
function node(label, x, y) {
  return { id: nextId++, label, x, y, word: '', done: false, children: [] };
}

function cloneTree(n) {
  return { ...n, children: n.children.map(cloneTree) };
}

function firstOpen(n) {
  if (!n.done && n.children.length === 0) return n;
  for (const c of n.children) {
    const found = firstOpen(c);
    if (found) return found;
  }
  return null;
}

function expand(focus, labels) {
  const gap = Math.max(92, 46 * labels.join('').length / Math.max(1, labels.length));
  const start = focus.x - gap * (labels.length - 1) / 2;
  focus.children = labels.map((label, i) => node(label, start + i * gap, focus.y + 82));
  focus.done = true;
}

function stepTree(root, previousGoals, currentGoals) {
  const tree = cloneTree(root);
  const focus = firstOpen(tree);
  if (!focus) return tree;

  const oldGoal = previousGoals[0] || { label: focus.label, target: '' };
  const labels = currentGoals.map(g => g.label);

  if (labels.length === 0 || labels[0] !== focus.label) {
    if (isZero(focus.label)) {
      focus.word = oldGoal.target === '' ? '∅' : oldGoal.target;
      focus.done = true;
      return tree;
    }
  }

  if (isXP(focus.label)) {
    if (labels[0] === barOf(focus.label)) {
      expand(focus, [barOf(focus.label)]);
    } else if (labels.length >= 2 && labels[1] === barOf(focus.label)) {
      expand(focus, [labels[0], labels[1]]);
    }
  } else if (isBar(focus.label)) {
    if (labels.length >= 2 && labels[0] === zeroOf(focus.label)) {
      expand(focus, [labels[0], labels[1]]);
    } else if (labels[0] === zeroOf(focus.label)) {
      expand(focus, [labels[0]]);
    } else if (labels.length >= 2 && labels[1] === focus.label) {
      expand(focus, [labels[0], labels[1]]);
    } else if (labels.length >= 2 && labels[0] === focus.label) {
      expand(focus, [labels[0], labels[1]]);
    }
  }
  return tree;
}

function collect(n, nodes, edges) {
  nodes.push(n);
  for (const c of n.children) {
    edges.push([n, c]);
    collect(c, nodes, edges);
  }
}

function TreeSvg({ root }) {
  const nodes = [], edges = [];
  collect(root, nodes, edges);
  const minX = Math.min(...nodes.map(n => n.x)) - 70;
  const maxX = Math.max(...nodes.map(n => n.x)) + 70;
  const maxY = Math.max(...nodes.map(n => n.y)) + 80;
  const width = Math.max(260, maxX - minX);
  return React.createElement('svg', {
      width: '100%',
      viewBox: `${minX} 0 ${width} ${maxY}`,
      style: { maxHeight: 560, overflow: 'visible' }
    },
    edges.map(([a, b]) => React.createElement('line', {
      key: 'e' + a.id + '-' + b.id,
      x1: a.x, y1: a.y + 18, x2: b.x, y2: b.y - 20,
      stroke: '#9aa7b2', strokeWidth: 2
    })),
    nodes.map(n => React.createElement('g', { key: n.id },
      React.createElement('rect', {
        x: n.x - 31, y: n.y - 20, rx: 14, width: 62, height: 34,
        fill: !n.done ? '#fff7d6' : '#e8f5ee',
        stroke: !n.done ? '#d4a017' : '#4f9d69',
        strokeWidth: 2
      }),
      React.createElement('text', {
        x: n.x, y: n.y + 2, textAnchor: 'middle',
        style: { fontWeight: 700, fontSize: 15, fill: '#203040' }
      }, n.label),
      n.word && React.createElement('text', {
        x: n.x, y: n.y + 39, textAnchor: 'middle',
        style: { fontSize: 14, fill: '#5a3d00' }
      }, n.word)
    ))
  );
}

export default function XTreeGrowth(props) {
  const goals = (props.goals || []).map(parseGoal);
  const signature = goals.map(g => g.label + ':' + g.target).join('|');
  const [root, setRoot] = React.useState(() => node(goals[0]?.label || 'CP', 500, 32));
  const previous = React.useRef(goals);
  const previousSignature = React.useRef(signature);

  React.useEffect(() => {
    if (signature === previousSignature.current) return;
    setRoot(r => stepTree(r, previous.current, goals));
    previous.current = goals;
    previousSignature.current = signature;
  }, [signature]);

  return React.createElement('div', {
      style: { border: '1px solid #d7dee8', borderRadius: 12, padding: 12, background: '#fbfcff', marginBottom: 12 }
    },
    React.createElement('div', { style: { fontWeight: 700, marginBottom: 8 } }, 'Live X-bar tree'),
    React.createElement(TreeSvg, { root }),
    React.createElement('div', { style: { color: '#6b7280', fontSize: 12, marginTop: 6 } },
      '绿色 = 已经生成的结构；黄色 = 当前正在建构的位置。已有节点不会重新布局。')
  );
}
"

end XSyntax
