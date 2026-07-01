/*
 * Informalization renderer — "the slides".
 * Copyright (c) 2026 Trail of Bits. Apache 2.0.
 *
 * SECURITY MODEL (DESIGN §9): every string that originates from the Lean module
 * reaches the DOM only via `document.createTextNode` / `.textContent`. We never
 * use `innerHTML`, `insertAdjacentHTML`, template-string HTML, `eval`, or
 * `new Function`. Structure is built from a fixed whitelist of element tags with
 * `document.createElement`. Input JSON is parsed with `JSON.parse` of an inert
 * <script type="application/json"> payload.
 *
 * Math: if KaTeX is vendored in ./vendor it is used (hardened config). Otherwise
 * a self-contained recursive-descent LaTeX typesetter renders to safe DOM
 * (sub/superscripts, fractions, roots, accents, full symbol set).
 */
'use strict';

(function () {
  // ===================================================================== //
  //  DOM helpers                                                          //
  // ===================================================================== //
  function el(tag, cls) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    return e;
  }
  function txt(s) { return document.createTextNode(s == null ? '' : String(s)); }

  // ===================================================================== //
  //  LaTeX → DOM math typesetter (self-contained, offline, safe)          //
  // ===================================================================== //
  var GREEK = {
    alpha:'α',beta:'β',gamma:'γ',delta:'δ',epsilon:'ϵ',varepsilon:'ε',zeta:'ζ',
    eta:'η',theta:'θ',vartheta:'ϑ',iota:'ι',kappa:'κ',lambda:'λ',mu:'μ',nu:'ν',
    xi:'ξ',omicron:'ο',pi:'π',varpi:'ϖ',rho:'ρ',varrho:'ϱ',sigma:'σ',varsigma:'ς',
    tau:'τ',upsilon:'υ',phi:'ϕ',varphi:'φ',chi:'χ',psi:'ψ',omega:'ω',
    Gamma:'Γ',Delta:'Δ',Theta:'Θ',Lambda:'Λ',Xi:'Ξ',Pi:'Π',Sigma:'Σ',
    Upsilon:'Υ',Phi:'Φ',Psi:'Ψ',Omega:'Ω'
  };
  var SYM = {
    circ:'∘',le:'≤',leq:'≤',ge:'≥',geq:'≥',neq:'≠',ne:'≠',equiv:'≡',approx:'≈',
    cong:'≅',times:'×',cdot:'⋅',div:'÷',pm:'±',mp:'∓',to:'→',rightarrow:'→',
    mapsto:'↦',gets:'←',leftarrow:'←',forall:'∀',exists:'∃',nexists:'∄',in:'∈',
    notin:'∉',ni:'∋',subseteq:'⊆',subset:'⊂',supseteq:'⊇',supset:'⊃',
    sqsubseteq:'⊑',cup:'∪',cap:'∩',sqcup:'⊔',sqcap:'⊓',emptyset:'∅',
    varnothing:'∅',wedge:'∧',land:'∧',vee:'∨',lor:'∨',neg:'¬',lnot:'¬',iff:'⟺',
    implies:'⟹',impliedby:'⟸',Rightarrow:'⇒',Leftarrow:'⇐',Leftrightarrow:'⇔',
    leftrightarrow:'↔',longrightarrow:'⟶',langle:'⟨',rangle:'⟩',lfloor:'⌊',
    rfloor:'⌋',lceil:'⌈',rceil:'⌉',infty:'∞',sum:'∑',prod:'∏',coprod:'∐',
    int:'∫',oint:'∮',partial:'∂',nabla:'∇',oplus:'⊕',ominus:'⊖',otimes:'⊗',
    odot:'⊙',vdash:'⊢',dashv:'⊣',models:'⊨',top:'⊤',bot:'⊥',setminus:'∖',
    mid:'∣',parallel:'∥',ldots:'…',cdots:'⋯',vdots:'⋮',ddots:'⋱',dots:'…',
    star:'⋆',ast:'∗',bullet:'∙',perp:'⊥',angle:'∠',triangle:'△',Box:'□',
    square:'□',diamond:'◇',sim:'∼',simeq:'≃',propto:'∝',preceq:'⪯',succeq:'⪰',
    prec:'≺',succ:'≻',ll:'≪',gg:'≫',subsetneq:'⊊',supsetneq:'⊋',aleph:'ℵ',
    hbar:'ℏ',ell:'ℓ',Re:'ℜ',Im:'ℑ',wp:'℘',backslash:'\\',colon:':',
    lnot2:'¬',land2:'∧',therefore:'∴',because:'∵',qed:'∎',blacksquare:'∎'
  };
  var BB = {N:'ℕ',Z:'ℤ',Q:'ℚ',R:'ℝ',C:'ℂ',F:'𝔽',H:'ℍ',P:'ℙ',E:'𝔼',D:'𝔻',A:'𝔸',G:'𝔾',K:'𝕂'};
  var CAL = {A:'𝒜',B:'ℬ',C:'𝒞',D:'𝒟',E:'ℰ',F:'ℱ',G:'𝒢',H:'ℋ',L:'ℒ',M:'ℳ',N:'𝒩',O:'𝒪',P:'𝒫',R:'ℛ',S:'𝒮',T:'𝒯'};
  var ACCENT = { bar:'̄', overline:'̄', hat:'̂', widehat:'̂',
    tilde:'̃', widetilde:'̃', vec:'⃗', dot:'̇', ddot:'̈', check:'̌' };
  var NAMED_OP = ['sin','cos','tan','cot','sec','csc','log','ln','exp','lim','max','min',
    'sup','inf','det','dim','ker','deg','gcd','arg','hom','mod'];

  // spacing class for an operator glyph (relations get room; brackets are tight)
  function opClass(ch) {
    if ('=<>≤≥≠≡≈≅≃∈∉∋⊆⊂⊇⊃⊑⊢⊣⊨↦→←↔⟶⟵⇒⇐⇔∣∥∼≪≫⪯⪰≺≻∝'.indexOf(ch) >= 0) return 'mo mo-rel';
    if ('+−±∓×⋅∘∪∩⊔⊓∧∨⊕⊖⊗⊙∖⋆∗·'.indexOf(ch) >= 0) return 'mo mo-bin';
    if (ch === '-') return 'mo mo-bin';
    if ('([{⟨⌊⌈'.indexOf(ch) >= 0) return 'mo mo-open';
    if (')]}⟩⌋⌉'.indexOf(ch) >= 0) return 'mo mo-close';
    if (',;:'.indexOf(ch) >= 0) return 'mo mo-punct';
    return 'mo';
  }

  // --- tokenizer-free recursive parser over a raw string ----------------
  function parseMath(str) {
    var i = 0, n = str.length;
    function readMacro() { // s[i] === '\\'
      i++;
      var m = /^[a-zA-Z]+/.exec(str.slice(i));
      if (m) { i += m[0].length; return m[0]; }
      var ch = str[i]; i++; return ch;            // \{  \}  \,  \;  etc.
    }
    function readBraced() { // s[i] === '{'  → raw inner string (balanced)
      i++; var depth = 1, out = '';
      while (i < n && depth > 0) {
        var c = str[i];
        if (c === '{') depth++;
        else if (c === '}') { depth--; if (depth === 0) { i++; break; } }
        out += c; i++;
      }
      return out;
    }
    // one argument: a braced group, a macro, or a single char
    function readArg() {
      while (i < n && str[i] === ' ') i++;
      if (i >= n) return '';
      if (str[i] === '{') return readBraced();
      if (str[i] === '\\') { var save = i; readMacro(); return str.slice(save, i); }
      var c = str[i]; i++; return c;
    }
    function macroNode(name) {
      if (name === 'frac' || name === 'dfrac' || name === 'tfrac') {
        var num = readArg(), den = readArg();
        var f = el('span', 'mfrac');
        var nu = el('span', 'mfrac-num'); nu.appendChild(parseMath(num));
        var de = el('span', 'mfrac-den'); de.appendChild(parseMath(den));
        f.appendChild(nu); f.appendChild(de);
        return f;
      }
      if (name === 'sqrt') {
        var rad = readArg();
        var s = el('span', 'msqrt');
        s.appendChild(txt('√'));
        var inner = el('span', 'msqrt-inner'); inner.appendChild(parseMath(rad));
        s.appendChild(inner);
        return s;
      }
      if (ACCENT[name]) {
        var a = readArg();
        var sp = el('span', 'mi');
        sp.appendChild(parseMath(a));
        sp.appendChild(txt(ACCENT[name]));   // combining mark
        return sp;
      }
      if (name === 'mathbb') { var g = readArg(); return txt(mapAlpha(g, BB)); }
      if (name === 'mathcal' || name === 'mathscr') { var g2 = readArg(); return txt(mapAlpha(g2, CAL)); }
      if (name === 'mathrm' || name === 'operatorname' || name === 'mathsf' ||
          name === 'mathbf' || name === 'mathtt') {
        var g3 = readArg(); var u = el('span', 'mathrm'); u.appendChild(parseMath(g3)); return u;
      }
      if (name === 'text' || name === 'textrm' || name === 'textit' || name === 'textbf' || name === 'mbox') {
        var g4 = readArg(); var t = el('span', 'mtext'); t.appendChild(txt(g4)); return t;
      }
      if (name === 'left' || name === 'right' || name === 'bigl' || name === 'bigr' ||
          name === 'big' || name === 'Big' || name === 'bigg' || name === 'Bigg' ||
          name === 'biggl' || name === 'biggr' || name === 'displaystyle' ||
          name === 'textstyle' || name === 'scriptstyle' || name === 'scriptscriptstyle' ||
          name === 'limits' || name === 'nolimits') {
        return null; // size/style hints: ignore, the delimiter char (if any) follows
      }
      if (name === ',' || name === ';' || name === ':' || name === ' ' || name === 'quad' || name === 'qquad')
        return txt(' ');
      if (name === '!') return null;
      if (name === '\\') return el('br');
      if (NAMED_OP.indexOf(name) >= 0) { var o = el('span', 'mop'); o.appendChild(txt(name)); return o; }
      if (GREEK[name]) return txt(GREEK[name]);
      if (SYM[name]) { var ms = el('span', opClass(SYM[name])); ms.appendChild(txt(SYM[name])); return ms; }
      // unknown macro → keep the word upright
      var unk = el('span', 'mathrm'); unk.appendChild(txt(name)); return unk;
    }
    function charNode(c) {
      if (/[A-Za-z]/.test(c)) { var mi = el('span', 'mi'); mi.appendChild(txt(c)); return mi; }
      if (/[0-9]/.test(c)) { var mn = el('span', 'mn'); mn.appendChild(txt(c)); return mn; }
      if ('+-=<>*/|().,:;[]'.indexOf(c) >= 0) { var mo = el('span', opClass(c)); mo.appendChild(txt(c)); return mo; }
      return txt(c);
    }
    function nextAtom() {
      while (i < n && str[i] === ' ') { i++; }
      if (i >= n) return null;
      var c = str[i];
      if (c === '{') return parseMath(readBraced());
      if (c === '\\') return macroNode(readMacro());
      if (c === '}') { i++; return null; }
      i++; return charNode(c);
    }

    var row = el('span', 'mrow');
    var last = null;
    while (i < n) {
      while (i < n && str[i] === ' ') i++;
      if (i >= n) break;
      var c = str[i];
      if (c === '_' || c === '^') {
        i++;
        var scr = parseMath(readArg());
        if (last && last.nodeType === 1) attachScript(last, c === '_' ? 'msub' : 'msup', scr);
        else { var base = el('span', 'mi'); attachScript(base, c === '_' ? 'msub' : 'msup', scr); row.appendChild(base); last = base; }
        continue;
      }
      var atom = nextAtom();
      if (atom) { row.appendChild(atom); if (atom.nodeType === 1) last = atom; }
    }
    return row;
  }

  function attachScript(baseEl, which, scriptNode) {
    // wrap base in a scripted span if not already; add sub/sup
    var holder;
    if (baseEl.classList && baseEl.classList.contains('scripts')) holder = baseEl;
    else {
      holder = el('span', 'scripts');
      baseEl.parentNode && baseEl.parentNode.replaceChild(holder, baseEl);
      var b = el('span', 'sbase'); b.appendChild(baseEl); holder.appendChild(b);
    }
    var s = el(which === 'msub' ? 'sub' : 'sup', which);
    s.appendChild(scriptNode);
    holder.appendChild(s);
    return holder;
  }

  function mapAlpha(s, table) {
    var out = '';
    for (var k = 0; k < s.length; k++) out += (table[s[k]] || s[k]);
    return out;
  }

  // ===================================================================== //
  //  Safe math entry point                                               //
  // ===================================================================== //
  function typesetInto(el_, latex, display) {
    var src = String(latex == null ? '' : latex);
    if (window.katex && typeof window.katex.render === 'function') {
      try {
        window.katex.render(src, el_, {
          throwOnError: false, trust: false, strict: 'ignore',
          maxExpand: 1000, displayMode: !!display
        });
        return;
      } catch (_e) { /* fall through */ }
    }
    el_.classList.add('math');
    if (display) el_.classList.add('math-display-inner');
    el_.appendChild(parseMath(src));
  }

  // ===================================================================== //
  //  Expansion budget (DESIGN §8)                                        //
  // ===================================================================== //
  var NODE_BUDGET = 80;
  var visibleCount = 0;

  function subtreeSize(node) {
    if (node == null) return 0;
    var k = 1;
    if (Array.isArray(node.xs)) node.xs.forEach(function (c) { k += subtreeSize(c); });
    ['body','summary','expanded','label','reveal','anchor','hint'].forEach(function (f) {
      if (node[f]) k += subtreeSize(node[f]);
    });
    return k;
  }

  // ===================================================================== //
  //  Explanation node renderer (tag whitelist only)                      //
  // ===================================================================== //
  function render(node) {
    if (node == null) return txt('');
    switch (node.kind) {
      case 'text': return txt(node.s);
      case 'math': {
        var sp = el('span', 'math-inline');
        typesetInto(sp, node.latex, false);
        if (node.prov) sp.setAttribute('data-prov', String(node.prov));
        return sp;
      }
      case 'displayMath': {
        var dv = el('div', 'math-display');
        typesetInto(dv, node.latex, true);
        if (node.prov) dv.setAttribute('data-prov', String(node.prov));
        return dv;
      }
      case 'concat': { var s = el('span', 'mrow-text'); (node.xs || []).forEach(function (c) { s.appendChild(render(c)); }); return s; }
      case 'paragraph': { var p = el('p'); (node.xs || []).forEach(function (c) { p.appendChild(render(c)); }); return p; }
      case 'indent': { var d = el('div', 'indent'); d.appendChild(render(node.body)); return d; }
      case 'detail': return renderDetail(node);
      case 'clickable': return renderClickable(node);
      case 'tooltip': return renderTooltip(node);
      case 'goalState': return renderGoal(node);
      default: { var u = el('span', 'unknown-node'); u.textContent = '⟨?⟩'; return u; }
    }
  }

  function renderClickable(node) {
    var span = el('span', 'clickable');
    var label = el('span', 'label'); label.appendChild(render(node.label));
    var reveal = el('span', 'reveal'); reveal.style.display = 'none';   // inline = cache-proof
    reveal.appendChild(render(node.reveal));
    span.appendChild(label); span.appendChild(reveal);
    label.addEventListener('click', function (ev) {
      ev.stopPropagation();
      reveal.style.display = (reveal.style.display === 'none') ? 'inline' : 'none';
    });
    return span;
  }

  function renderTooltip(node) {
    var span = el('span', 'tooltip-anchor');
    span.setAttribute('tabindex', '0');
    span.appendChild(render(node.anchor));
    var hint = el('span', 'tooltip-hint'); hint.setAttribute('role', 'tooltip');
    hint.style.display = 'none';                 // inline = cache-proof
    hint.appendChild(render(node.hint));
    span.appendChild(hint);
    function show() { hint.style.display = 'block'; }
    function hide() { hint.style.display = 'none'; }
    span.addEventListener('mouseenter', show);
    span.addEventListener('mouseleave', hide);
    span.addEventListener('focus', show);
    span.addEventListener('blur', hide);
    return span;
  }

  function renderDetail(node) {
    var wrap = el('span', 'detail' + (node.salient ? ' salient' : ''));
    var toggle = el('button', 'toggle'); toggle.type = 'button';
    toggle.setAttribute('aria-expanded', 'false'); toggle.textContent = '⊕';
    var summary = el('span', 'summary'); summary.appendChild(render(node.summary));
    // Visibility is controlled by INLINE style, not a CSS class, so a stale or
    // missing stylesheet can never leave hidden detail exposed.
    var expanded = el('span', 'expanded'); expanded.style.display = 'none';
    var built = false;
    toggle.addEventListener('click', function (ev) {
      ev.stopPropagation();
      var isOpen = expanded.style.display !== 'none';
      if (isOpen) {
        expanded.style.display = 'none'; summary.style.display = '';
        toggle.textContent = '⊕'; toggle.setAttribute('aria-expanded', 'false');
      } else {
        if (!built) {
          var sz = subtreeSize(node.expanded);
          if (visibleCount + sz > NODE_BUDGET && !window.confirm('Expand ' + sz + ' steps? (exceeds view budget)')) return;
          expanded.appendChild(render(node.expanded)); visibleCount += sz; built = true;
        }
        expanded.style.display = 'block'; summary.style.display = 'none';
        toggle.textContent = '⊖'; toggle.setAttribute('aria-expanded', 'true');
      }
    });
    wrap.appendChild(toggle); wrap.appendChild(summary); wrap.appendChild(expanded);
    return wrap;
  }

  function renderGoal(node) {
    var box = el('div', 'goal-state');
    var hyps = Array.isArray(node.hyps) ? node.hyps : [];
    function hypLine(h) {
      var line = el('div', 'hyp' + (h.changed ? ' changed' : ''));
      var nm = el('span', 'hyp-name'); nm.appendChild(txt(h.name));
      line.appendChild(nm);
      // English-style: omit " : type" when there is no type (a plain stated fact)
      if (h.type && String(h.type).trim() !== '') {
        line.appendChild(txt(' : '));
        var ty = el('span', 'hyp-type'); typesetInto(ty, h.type, false); line.appendChild(ty);
      }
      return line;
    }
    var changed = hyps.filter(function (h) { return h && h.changed; });
    var rest = hyps.filter(function (h) { return !(h && h.changed); });
    changed.forEach(function (h) { box.appendChild(hypLine(h)); });
    if (rest.length) {
      var ctx = el('details', 'context-fold');
      var sum = el('summary'); sum.appendChild(txt(rest.length + ' more hypothes' + (rest.length === 1 ? 'is' : 'es')));
      ctx.appendChild(sum); rest.forEach(function (h) { ctx.appendChild(hypLine(h)); });
      box.appendChild(ctx);
    }
    box.appendChild(el('hr'));
    var goal = el('div', 'goal');
    var ts = el('span', 'turnstile'); ts.appendChild(txt('⊢ ')); goal.appendChild(ts);
    var g = el('span'); typesetInto(g, node.goal || '', false); goal.appendChild(g);
    box.appendChild(goal);
    return box;
  }

  // ===================================================================== //
  //  Mount                                                               //
  // ===================================================================== //
  function mount() {
    var dataEl = document.getElementById('informalization-data');
    var root = document.getElementById('doc-root');
    if (!dataEl || !root) return;
    var doc;
    try { doc = JSON.parse(dataEl.textContent); }
    catch (e) { root.appendChild(txt('Could not parse explanation data.')); return; }

    if (doc && doc.title) { var h = el('h1'); h.appendChild(txt(doc.title)); root.appendChild(h); }
    var body = (doc && doc.body) ? doc.body : doc;
    visibleCount = 0;
    root.appendChild(render(body));

    document.addEventListener('keydown', function (ev) {
      if (ev.key === 'g') document.querySelectorAll('.context-fold').forEach(function (d) { d.open = !d.open; });
    });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', mount);
  else mount();
})();
