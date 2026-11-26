/*
 * The protocol widget of the ArkLib protocol specifications site.
 *
 * Each `.spec-widget` element holds, in a JSON script, what Lean computed from one or more
 * specifications when the site was built: the JSON skeleton (schema arklib-protocol-skeleton/2),
 * the counts the skeleton was built at, the folded and expanded `cryptocode` figures, and the
 * expanded figure at more sizes. This script draws five views from that data.
 *
 * The figure is drawn by a port of the walk in Specs/Export.lean (`Skel.texGo`). The same walk
 * prints LaTeX, and on load the script compares that LaTeX with every figure Lean produced, byte
 * for byte. The footer reports the result so that the reader can see that the page unrolls loops
 * and prints formulas the way Lean does.
 */
(function () {
  "use strict";

  const hasOwn = (o, k) => Object.prototype.hasOwnProperty.call(o, k);
  const esc = (s) =>
    String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
  const math = (tex) => `<span class="sw-math" data-tex="${esc(tex)}">${esc(tex)}</span>`;
  const annot = (tex) => `<span class="sw-annot" title="Annotation: Lean does not check this text">${math(tex)}</span>`;

  /* Render every math placeholder under `root` with KaTeX, which Verso loads on every page. */
  function typeset(root) {
    const katex = window.katex;
    for (const el of root.querySelectorAll(".sw-math")) {
      if (el.dataset.done) continue;
      el.dataset.done = "1";
      if (!katex) continue;
      try {
        katex.render(el.dataset.tex, el, { throwOnError: false, displayMode: false });
      } catch (e) {
        el.textContent = el.dataset.tex;
      }
    }
  }

  /* ------------------------------------------------------------------------------------------
   * The printer, ported from Specs/Formula.lean (Ix.tex, Name.tex, Name.texAt, Syn.tex).
   * A mode is folded (every symbol prints as itself) or expanded (a bound symbol prints as its
   * value). `env` maps symbols to numbers; a later binding shadows an earlier one, as
   * `Mode.bind` does.
   * ---------------------------------------------------------------------------------------- */
  const FOLDED = { folded: true, env: {} };
  const bind = (md, v, k) => ({ folded: md.folded, env: { ...md.env, [v]: k } });
  const symTex = (v, off) => (off === 0 ? v : off > 0 ? `${v}+${off}` : `${v}-${-off}`);
  function ixTex(md, ix) {
    if (hasOwn(ix, "num")) return String(ix.num);
    if (!md.folded && hasOwn(md.env, ix.symbol)) return String(md.env[ix.symbol] + ix.offset);
    return symTex(ix.symbol, ix.offset);
  }
  function nameTex(md, nm) {
    const s = nm.sub;
    if (!s) return nm.base;
    if (s.kind === "at") return `${nm.base}_{${ixTex(md, s.index)}}`;
    if (s.kind === "below") return `${nm.base}_{<${ixTex(md, s.index)}}`;
    return `${nm.base}_{${s.symbol}}`;
  }
  function nameTexAt(md, nm, i) {
    const s = nm.sub;
    if (!s) return `${nm.base}_{${i}}`;
    if (s.kind === "at") return `${nm.base}_{${ixTex(md, s.index)},${i}}`;
    if (s.kind === "sym") return `${nm.base}_{${s.symbol},${i}}`;
    return `{${nameTex(md, nm)}}_{${i}}`;
  }
  const BIN = { and: [10, " \\land "], eq: [20, " = "], add: [30, " + "], sub: [30, " - "], mul: [40, " \\cdot "] };
  const prec = (s) => (BIN[s.op] ? BIN[s.op][0] : s.op === "sum" || s.op === "prod" ? 25 : s.op === "neg" ? 35 : 100);
  const par = (b, s) => (b ? `(${s})` : s);
  function synTex(md, s) {
    switch (s.op) {
      case "var": return nameTex(md, s.name);
      case "lit": return s.tex;
      case "neg": return "-" + par(prec(s.args[0]) < 100, synTex(md, s.args[0]));
      case "pow": return par(prec(s.args[0]) < 100, synTex(md, s.args[0])) + `^{${s.exp}}`;
      case "sum": case "prod":
        return `\\${s.op}_{${nameTex(md, s.var)} \\in ${s.domain}} ` + par(prec(s.body) <= 30, synTex(md, s.body));
      case "query": return `${nameTex(md, s.oracle)}(${synTex(md, s.arg)})`;
      case "app": return `\\mathrm{${s.fn}}(${synTex(md, s.arg)})`;
      case "index": {
        const [f, i] = s.args;
        if (f.op === "var") return nameTexAt(md, f.name, synTex(md, i));
        return `{${par(prec(f) < 100, synTex(md, f))}}_{${synTex(md, i)}}`;
      }
      default: {
        const [p, t] = BIN[s.op];
        const [a, b] = s.args;
        return par(prec(a) < p, synTex(md, a)) + t + par(prec(b) <= p, synTex(md, b));
      }
    }
  }

  /* Every "tex" field in the JSON is Lean's folded rendering of the node next to it. */
  function checkFormulas(sk) {
    let ok = 0;
    const bad = [];
    const test = (got, want) => (got === want ? ok++ : bad.push([got, want]));
    const walk = (x) => {
      if (Array.isArray(x)) return x.forEach(walk);
      if (!x || typeof x !== "object") return;
      if (x.syntax && typeof x.tex === "string") test(synTex(FOLDED, x.syntax), x.tex);
      else if (hasOwn(x, "base") && typeof x.tex === "string") test(nameTex(FOLDED, x), x.tex);
      Object.values(x).forEach(walk);
    };
    walk(sk.body);
    return { ok, bad };
  }

  /* ------------------------------------------------------------------------------------------
   * The walk of Specs/Export.lean (TexState and Skel.texGo), over the JSON's nested nodes.
   *
   * Lean walks a flat skeleton with stage markers; the JSON nests a stage's items in its node. A
   * stage's body therefore continues the sequence it is in (no flush at its end), while a loop's
   * body and a branch case's body are whole skeletons (flush at the end). Since a branch or an
   * opaque message ends the sequence, a stage whose body ends with one closes inside the cases.
   *
   * Each line keeps, next to its LaTeX, what the HTML figure needs: the divisions before it and the
   * node it prints with the mode in force.
   * ---------------------------------------------------------------------------------------- */
  const texAnnot = (s) => `\\specannot{${s}}`;
  const withNote = (line, note) => (note ? `${line} \\quad ${texAnnot(note)}` : line);
  const noteText = (n) => (n ? n.text : "");

  function moveLine(md, kind, nm, ty, hn, note) {
    const n = nameTex(md, nm);
    const prover = hn ? `${n} \\gets ${texAnnot(hn)}` : "";
    let line;
    if (kind === "message") line = `${prover} \\< \\sendmessageright*{${n} \\in ${ty}} \\< `;
    else if (kind === "oracle") line = `${prover} \\< \\sendmessageright*{[\\![${n}]\\!] \\in ${ty}} \\< `;
    else line = ` \\< \\sendmessageleft*{${n}} \\< ${n} \\sample ${ty}`;
    return withNote(line, note);
  }

  function newState(folded, counts) {
    return { md: { folded, env: {} }, counts: { ...counts }, stages: [], pending: [], lines: [] };
  }
  function emit(st, tex, row) {
    st.lines.push({ divs: st.pending, tex, row });
    st.pending = [];
  }
  const divide = (st, d) => st.pending.push(d);
  function flush(st) {
    if (st.pending.length) emit(st, " \\< \\< ", null);
  }
  const endsSequence = (nodes) => nodes.length > 0 && ["branch", "opaque"].includes(nodes[nodes.length - 1].kind);

  function roundDiv(n, folded, j) {
    if (folded) {
      const err = n.error ? `; error $${texAnnot(n.error.text)}$` : "";
      return { k: "round", n, folded, tex: `\\textsf{${n.block}}: round $${n.var}$ of $${n.count}$${err}` };
    }
    return { k: "round", n, folded, j, tex: `\\textsf{${n.block}}: round ${j}` };
  }
  function stageEnd(st) {
    if (!st.stages.length) return;
    const s = st.stages.pop();
    divide(st, { k: "stage-end", name: s.name, formula: s.output, md: st.md,
      tex: `end of stage \\textsf{${s.name}}: $${synTex(st.md, s.output.syntax)}$` });
  }

  function walkSeq(nodes, st) {
    for (const n of nodes) walkNode(n, st);
  }
  function walkSkel(nodes, st) {
    walkSeq(nodes, st);
    flush(st);
  }
  function walkNode(n, st) {
    const md = st.md;
    switch (n.kind) {
      case "move":
        emit(st, moveLine(md, n.move, n.name, n.type, noteText(n.honest), noteText(n.note)), { k: "move", n, md });
        break;
      case "input":
        emit(st, ` \\< \\< \\text{input oracle } [\\![${nameTex(md, n.name)}]\\!] \\in ${n.type}`, { k: "input", n, md });
        break;
      case "check":
        emit(st, withNote(` \\< \\< \\text{check } ${synTex(md, n.formula.syntax)}`, noteText(n.note)), { k: "check", n, md });
        break;
      case "let":
        emit(st, withNote(` \\< \\< ${nameTex(md, n.name)} := ${synTex(md, n.formula.syntax)}`, noteText(n.note)), { k: "let", n, md });
        break;
      case "stage":
        divide(st, { k: "stage", name: n.name, formula: n.input, md,
          tex: `stage \\textsf{${n.name}}: $${synTex(md, n.input.syntax)}$` });
        st.stages.push({ name: n.name, output: n.output });
        walkSeq(n.body, st);
        if (!endsSequence(n.body)) stageEnd(st);
        break;
      case "end":
        if (n.of === "stage") stageEnd(st);
        break;
      case "loop": {
        if (md.folded) {
          divide(st, roundDiv(n, true, 0));
          walkSkel(n.body, st);
          st.md = md;
          divide(st, { k: "loop-end", n, tex: `end of loop \\textsf{${n.block}}` });
        } else {
          const N = hasOwn(st.counts, n.count) ? st.counts[n.count] : 0;
          const m = bind(md, n.count, N);
          for (let j = 0; j < N; j++) {
            divide(st, roundDiv(n, false, j));
            st.md = bind(m, n.var, j);
            walkSkel(n.body, st);
          }
          st.md = m;
          divide(st, { k: "loop-end", n, rounds: N, tex: `end of loop \\textsf{${n.block}}` });
        }
        break;
      }
      case "branch": {
        emit(st, moveLine(md, "message", n.on, n.type, noteText(n.honest), ""), { k: "move", n: { ...n, move: "message", owner: "prover", name: n.on }, md });
        const base = { md: st.md, counts: st.counts, stages: st.stages, pending: [] };
        for (const c of n.cases) {
          const v = Number(c.value);
          const counts = !n.on.sub && Number.isInteger(v) ? { ...base.counts, [n.on.base]: v } : base.counts;
          const cs = { md: base.md, counts, stages: [...base.stages], pending: [], lines: st.lines };
          divide(cs, { k: "case", on: n.on, value: c.value, md: base.md,
            tex: `case $${nameTex(base.md, n.on)} = ${c.value}$` });
          walkSkel(c.body, cs);
          st.lines = cs.lines;
        }
        st.pending = [];
        break;
      }
      case "opaque":
        emit(st, moveLine(md, "message", n.on, n.type, noteText(n.honest), ""), { k: "move", n: { ...n, move: "message", owner: "prover", name: n.on }, md });
        emit(st, ` \\< \\< \\text{the rest depends on } ${nameTex(md, n.on)}`, { k: "rest", n, md });
        break;
      default:
        break;
    }
  }

  /* The walk of a whole skeleton: folded from the erased skeleton, or expanded at `counts`. */
  function walk(sk, folded, counts) {
    const st = newState(folded, folded ? {} : counts);
    walkSkel(sk.body, st);
    return st.lines;
  }

  /* Skel.toTex: the cryptocode figure of the walk. */
  function toTex(title, folded, lines) {
    const all = [{ divs: [], tex: "\\textbf{Prover} \\< \\< \\textbf{Verifier}" }, ...lines];
    const body = all.map((l, k) => {
      const pre = l.divs.length ? `\\pcintertext[dotted]{${l.divs.map((d) => d.tex).join("; ")}}\n` : "";
      const post = k + 1 === all.length ? "" : all[k + 1].divs.length ? " \\pclb" : " \\\\";
      return pre + l.tex + post;
    });
    return "% Generated by docs/design/interaction-layer/prototypes/Specs/Export.lean.\n" +
      "% Requires \\usepackage{amsmath,amssymb} and \\usepackage{cryptocode}.\n" +
      "\\providecommand{\\specannot}[1]{\\textcolor{gray}{#1}}\n" +
      "\\begin{figure}\n\\centering\n\\procedure{" + title + "}{%\n" +
      body.join("\n") +
      "\n}\n\\caption{" + title + (folded ? ", one generic round of each loop" : "") +
      ", generated from the skeleton. Gray text is annotation that Lean does not check.}\n" +
      "\\end{figure}\n";
  }

  const countsText = (cs) => {
    const ks = Object.keys(cs);
    return ks.length ? ks.map((k) => `${k} = ${cs[k]}`).join(", ") : "its only size";
  };
  const sameCounts = (a, b) => {
    const ka = Object.keys(a), kb = Object.keys(b);
    return ka.length === kb.length && ka.every((k) => b[k] === a[k]);
  };

  /* Compare the port with every figure Lean produced for an example. */
  function crossCheck(ex) {
    const sk = ex.skeleton;
    const runs = [{ folded: true, counts: {}, want: ex.tex }, { folded: false, counts: ex.counts, want: ex.texExpanded }]
      .concat((ex.samples || []).map((s) => ({ folded: false, counts: s.counts, want: s.tex })));
    const res = runs.map((r) => ({ ...r, ok: toTex(ex.title, r.folded, walk(sk, r.folded, r.counts)) === r.want }));
    return { runs: res, formulas: checkFormulas(sk) };
  }

  /* ------------------------------------------------------------------------------------------
   * The figure, drawn from the walk's lines.
   * ---------------------------------------------------------------------------------------- */
  let arrowId = 0;
  function arrowSvg(dir) {
    const c = dir === "right" ? "var(--sw-prover)" : "var(--sw-verifier)";
    const id = "sw-ah" + arrowId++;
    const x1 = dir === "right" ? 4 : 96, x2 = dir === "right" ? 96 : 4;
    return `<svg viewBox="0 0 100 12" preserveAspectRatio="none" aria-hidden="true"><defs><marker id="${id}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="${c}"/></marker></defs><line x1="${x1}" y1="6" x2="${x2}" y2="6" stroke="${c}" stroke-width="1.6" vector-effect="non-scaling-stroke" marker-end="url(#${id})"/></svg>`;
  }
  const noteOf = (n) => (n.note ? ` ${annot(n.note.text)}` : "");
  const vRow = (html) => `<div class="sw-cell"></div><div class="sw-cell"></div><div class="sw-cell sw-r">${html}</div>`;
  const band = (html, right, cls) => `<div class="sw-band ${cls || ""}"><span>${html}</span><span class="sw-err">${right || ""}</span></div>`;

  function rowHtml(r) {
    const { n, md } = r;
    switch (r.k) {
      case "move": {
        const nm = nameTex(md, n.name);
        if (n.move === "challenge") {
          return `<div class="sw-cell"></div><div class="sw-arrow"><div class="sw-lbl">${math(nm)}</div>${arrowSvg("left")}</div><div class="sw-cell sw-r">${math(nm + " \\xleftarrow{\\$} " + n.type)}${noteOf(n)}</div>`;
        }
        const honest = n.honest ? `${math(nm + " \\gets")} ${annot(n.honest.text)}` : "";
        const lbl = n.move === "oracle"
          ? `${math("[\\![" + nm + "]\\!] \\in " + n.type)} <span class="sw-tag sw-oracle">oracle</span>`
          : math(nm + " \\in " + n.type);
        return `<div class="sw-cell">${honest}</div><div class="sw-arrow"><div class="sw-lbl">${lbl}</div>${arrowSvg("right")}</div><div class="sw-cell sw-r">${noteOf(n)}</div>`;
      }
      case "input":
        return vRow(`<span class="sw-tag sw-input">input oracle</span> ${math("[\\![" + nameTex(md, n.name) + "]\\!] \\in " + n.type)}`);
      case "check":
        return vRow(`<span class="sw-chk">${math(synTex(md, n.formula.syntax))}</span><span class="sw-tag sw-check">check · ${esc(n.label)}</span>${noteOf(n)}`);
      case "let":
        return vRow(`${math(nameTex(md, n.name) + " := " + synTex(md, n.formula.syntax))}<span class="sw-tag sw-let">let</span>${noteOf(n)}`);
      case "rest":
        return vRow(`the rest depends on ${math(nameTex(md, n.on))}`);
      default:
        return "";
    }
  }
  function divHtml(d) {
    switch (d.k) {
      case "stage":
        return band(`stage <b>${esc(d.name)}</b>`, `claim in: ${math(synTex(d.md, d.formula.syntax))}`, "sw-stage");
      case "stage-end":
        return band(`end of stage <b>${esc(d.name)}</b>`, `claim out: ${math(synTex(d.md, d.formula.syntax))}`, "sw-stage-end");
      case "round": {
        const err = d.n.error ? `error ${annot(d.n.error.text)}` : "";
        return d.folded
          ? band(`<b>${esc(d.n.block)}</b>: round ${math(d.n.var)} of ${math(d.n.count)}`, err, "sw-round")
          : band(`<b>${esc(d.n.block)}</b>: round ${d.j}`, err, "sw-round");
      }
      case "loop-end":
        return band(`end of loop <b>${esc(d.n.block)}</b>${d.rounds === 0 ? ` · no rounds, since ${math(d.n.count + " = 0")}` : ""}`, "", "sw-loop-end");
      case "case":
        return band(`case ${math(nameTex(d.md, d.on) + " = " + d.value)}`, "", "sw-case");
      default:
        return "";
    }
  }
  function figureHtml(lines) {
    const out = [`<div class="sw-fig"><div class="sw-head sw-p">Prover</div><div class="sw-head"></div><div class="sw-head sw-v">Verifier</div>`];
    for (const l of lines) {
      for (const d of l.divs) out.push(divHtml(d));
      if (l.row) out.push(rowHtml(l.row));
    }
    out.push("</div>");
    return out.join("");
  }

  /* The count symbols of a skeleton's loops that no branch case fixes, in order of appearance. */
  function freeCounts(nodes, bound = new Set(), acc = []) {
    for (const n of nodes) {
      if (n.kind === "loop") {
        if (!bound.has(n.count) && !acc.includes(n.count)) acc.push(n.count);
        freeCounts(n.body, bound, acc);
      } else if (n.kind === "stage") freeCounts(n.body, bound, acc);
      else if (n.kind === "branch") for (const c of n.cases) freeCounts(c.body, n.on.sub ? bound : new Set([...bound, n.on.base]), acc);
    }
    return acc;
  }

  /* ------------------------------------------------------------------------------------------
   * The claim flow: each stage's input and output claims, as formulas.
   * ---------------------------------------------------------------------------------------- */
  function stagesOf(nodes, acc = []) {
    for (const n of nodes) {
      if (n.kind === "stage") { acc.push(n); stagesOf(n.body, acc); }
      else if (n.kind === "branch") { const c = n.cases[n.cases.length - 1]; if (c) stagesOf(c.body, acc); }
    }
    return acc;
  }
  function topLevel(sk) {
    const inputs = [], checks = [];
    const go = (nodes, depth) => {
      for (const n of nodes) {
        if (n.kind === "input") inputs.push(n);
        else if (n.kind === "check" && depth === 0) checks.push(n);
        else if (n.kind === "branch") { const c = n.cases[n.cases.length - 1]; if (c) go(c.body, depth); }
      }
    };
    go(sk.body, 0);
    return { inputs, checks };
  }
  function claimsHtml(sk) {
    const md = FOLDED;
    const st = stagesOf(sk.body);
    const { inputs, checks } = topLevel(sk);
    const box = (cls, title, body) => `<div class="sw-cbox ${cls}"><div class="sw-ctitle">${title}</div>${body}</div>`;
    const parts = [];
    parts.push(box("sw-term", "Input", inputs.length
      ? `<div class="sw-small">input oracles ${inputs.map((n) => math(nameTex(md, n.name))).join(", ")}</div>`
      : `<div class="sw-small sw-muted">statement only</div>`));
    if (!st.length) {
      parts.push(`<div class="sw-cedge"><span class="sw-muted sw-small">no stage declares a claim</span></div>`);
      parts.push(box("sw-note", "No stages", `<p class="sw-small">Because this example has rounds and checks but no <code>stage</code>, it declares no input or output claim. Its security statements would use problems written by hand.</p>`));
    }
    st.forEach((s, k) => {
      const prev = st[k - 1];
      const shared = prev && JSON.stringify(prev.output.syntax) === JSON.stringify(s.input.syntax);
      parts.push(`<div class="sw-cedge">${shared ? `<span class="sw-tag sw-shared">same formula as the previous output claim</span>` : ""}<span class="sw-small">${math(synTex(md, s.input.syntax))}</span></div>`);
      const loops = [];
      const collect = (nodes) => nodes.forEach((n) => { if (n.kind === "loop") { loops.push(n); collect(n.body); } });
      collect(s.body);
      parts.push(box("sw-stagebox", `stage ${esc(s.name)}`, `<div class="sw-small sw-muted">${loops.map((r) => `${esc(r.block)}: ${math(r.count)} rounds${r.error ? ", error " + annot(r.error.text) + " each" : ""}`).join("; ") || "no rounds"}</div>`));
      parts.push(`<div class="sw-cedge"><span class="sw-small">${math(synTex(md, s.output.syntax))}</span></div>`);
    });
    if (checks.length) parts.push(box("sw-checkbox", "Final checks", checks.map((c) => `<div class="sw-small"><span class="sw-tag sw-check">${esc(c.label)}</span> ${math(synTex(md, c.formula.syntax))}</div>`).join("")));
    parts.push(box("sw-term", "Output", `<div class="sw-small sw-muted">the verifier's output, if every check passed</div>`));
    return `<div class="sw-cflow">${parts.join("")}</div>`;
  }

  /* ------------------------------------------------------------------------------------------
   * The transcript, with the label path of each move. The rule is Lean's (Specs/Run.lean,
   * findMove): an accessor reads the first move, in skeleton order, whose enclosing stages, loops
   * and rounds contain the path's names as a subsequence and whose name matches the label: its
   * base, or its base with its subscript (v_A, "\\alpha_2").
   * ---------------------------------------------------------------------------------------- */
  const isIdent = (s) => /^[A-Za-z_][A-Za-z0-9_']*$/.test(s);
  const isCase = (c) => c.includes(" = ");
  function dedupe(cs) { const out = []; for (const c of cs) if (out[out.length - 1] !== c) out.push(c); return out; }
  function isSubseq(l, ctx) { let k = 0; for (const c of ctx) if (k < l.length && l[k] === c) k++; return k === l.length; }
  function subText(nm, env) {
    const s = nm.sub;
    if (!s) return null;
    if (s.kind === "sym") return s.symbol;
    if (s.kind === "at") {
      const i = s.index;
      if (hasOwn(i, "num")) return String(i.num);
      return hasOwn(env, i.symbol) ? String(env[i.symbol] + i.offset) : null;
    }
    return null;
  }
  function hits(nm, env, lab) {
    if (nm.base === lab) return true;
    const t = subText(nm, env);
    return t != null && (lab === `${nm.base}_${t}` || lab === `${nm.base}_{${t}}`);
  }
  function accessorFor(items, idx) {
    const it = items[idx], nm = it.n.name;
    const path = dedupe(it.ctx);
    const names = path.filter((c) => !isCase(c));
    const first = (lab) => items.findIndex((o) => o.n.kind === "move" && isSubseq(names, o.ctx.filter((c) => !isCase(c))) && hits(o.n.name, o.env, lab));
    const t = subText(nm, it.env);
    for (const lab of [nm.base, t != null ? `${nm.base}_${t}` : null]) {
      if (lab && first(lab) === idx) return { ok: true, text: `tr⟦${[...path, isIdent(lab) ? lab : JSON.stringify(lab)].join(", ")}⟧` };
    }
    return { ok: false, text: "no label path reads this move" };
  }
  /* The moves, checks and local values in transcript order, with every loop unrolled to its
   * count. Each item keeps the symbols bound around it and its label context. */
  function flatten(sk, caseIdx, counts) {
    const items = [];
    const go = (nodes, ctx, grp, env, cnt) => {
      for (const n of nodes) {
        if (n.kind === "move" || n.kind === "check" || n.kind === "let") items.push({ n, ctx, grp, env });
        else if (n.kind === "stage") env = go(n.body, [...ctx, n.name], n.name, env, cnt);
        else if (n.kind === "loop") {
          const N = hasOwn(cnt, n.count) ? cnt[n.count] : 0;
          const e = { ...env, [n.count]: N };
          for (let j = 0; j < N; j++) go(n.body, [...ctx, n.block, String(j)], `${n.block} ${j}`, { ...e, [n.var]: j }, cnt);
          env = e;
        } else if (n.kind === "branch" || n.kind === "opaque") {
          items.push({ n: { kind: "move", move: "message", owner: "prover", name: n.on, type: n.type, honest: n.honest }, ctx, grp, env });
          if (n.kind === "opaque") continue;
          const c = n.cases[Math.min(caseIdx, n.cases.length - 1)];
          if (!c) continue;
          const v = Number(c.value);
          const cnt2 = !n.on.sub && Number.isInteger(v) ? { ...cnt, [n.on.base]: v } : cnt;
          go(c.body, [...ctx, `${n.on.base} = ${c.value}`], `case ${c.value}`, env, cnt2);
        }
      }
      return env;
    };
    go(sk.body, [], "", {}, { ...counts });
    return items;
  }
  function firstBranch(nodes) {
    for (const n of nodes) {
      if (n.kind === "branch") return n;
      const b = n.body && firstBranch(n.body);
      if (b) return b;
    }
    return null;
  }
  /* The accessor paths of the transcript view at the example's own sizes, in every branch case,
   * against the paths that Lean elaborated when the site was built (ex.accessors, from path to
   * type). SpecSite/Meta/Accessors.lean computes Lean's list by the same rule. */
  function accCheck(ex) {
    if (!ex.accessors) return null;
    const sk = ex.skeleton, br = firstBranch(sk.body), page = [];
    const cases = br ? Math.max(1, br.cases.length) : 1;
    for (let c = 0; c < cases; c++) {
      const items = flatten(sk, c, ex.counts || {});
      items.forEach((it, i) => {
        if (it.n.kind !== "move") return;
        const a = accessorFor(items, i);
        if (a.ok && !page.includes(a.text)) page.push(a.text);
      });
    }
    const missing = page.filter((a) => !hasOwn(ex.accessors, a));
    const extra = Object.keys(ex.accessors).filter((a) => !page.includes(a));
    return { n: page.length, cases, ok: missing.length === 0 && extra.length === 0, missing, extra };
  }
  const GREEK = { tau: "τ", rho: "ρ", alpha: "α", beta: "β", gamma: "γ", omega: "ω", delta: "δ" };
  const glyph = (n) => n.kind === "check" ? "✓" : n.kind === "let" ? "≔"
    : esc(n.name.base.replace(/\\([a-zA-Z]+)/g, (_, w) => GREEK[w] || "").replace(/[{}~]/g, "").slice(0, 3) || "·");
  function timelineHtml(items) {
    const groups = [];
    for (const it of items) {
      const g = groups[groups.length - 1];
      if (g && g.key === it.grp) g.items.push(it); else groups.push({ key: it.grp, items: [it] });
    }
    const owner = (it) => (it.n.kind === "move" ? it.n.owner : "verifier");
    const kcls = (n) => n.kind === "move" ? (n.move === "oracle" ? "sw-k-oracle" : n.move === "challenge" ? "sw-k-challenge" : "sw-k-message") : n.kind === "check" ? "sw-k-check" : "sw-k-let";
    const row = (who) => groups.map((g) => `<div class="sw-tl-grp"><span class="sw-tl-lab">${who === "prover" ? esc(g.key) || "&nbsp;" : "&nbsp;"}</span><div class="sw-tl-cells">${g.items.map((it) => owner(it) === who
      ? `<button type="button" class="sw-tl-cell ${kcls(it.n)}" data-i="${items.indexOf(it)}" aria-label="${esc(it.n.kind)}">${glyph(it.n)}</button>`
      : `<span class="sw-tl-cell sw-tl-gap"></span>`).join("")}</div></div>`).join("");
    return `<div class="sw-tl">
      <div class="sw-tl-row"><span class="sw-who sw-p">Prover</span><div class="sw-tl-track">${row("prover")}</div></div>
      <div class="sw-tl-row"><span class="sw-who sw-v">Verifier</span><div class="sw-tl-track">${row("verifier")}</div></div>
      <div class="sw-tl-row"><span class="sw-who sw-muted">Step</span><div class="sw-tl-detail">Select a cell.</div></div></div>`;
  }

  /* ------------------------------------------------------------------------------------------
   * One widget.
   * ---------------------------------------------------------------------------------------- */
  const VIEWS = [["figure", "Figure"], ["claims", "Claim flow"], ["timeline", "Transcript"], ["tex", "LaTeX"], ["json", "JSON"]];
  const MAX_COUNT = 12;
  const seg = (cls, opts, cur, label) =>
    `<div class="sw-seg ${cls}" role="group" aria-label="${esc(label)}">${opts.map(([v, l]) => `<button type="button" data-x="${esc(v)}" aria-pressed="${v === cur}">${esc(l)}</button>`).join("")}</div>`;
  const legend = `<span class="sw-legend"><i class="sw-sw-prover"></i>prover</span><span class="sw-legend"><i class="sw-sw-verifier"></i>verifier</span><span class="sw-legend"><i class="sw-sw-oracle"></i>oracle</span><span class="sw-legend"><i class="sw-sw-check"></i>check</span><span class="sw-legend"><i class="sw-sw-annot"></i>gray: annotation, unchecked</span>`;

  function mount(root) {
    let data;
    try {
      data = JSON.parse(root.querySelector("script.spec-widget-data").textContent);
    } catch (e) {
      return;
    }
    const fallback = root.querySelector(".spec-widget-fallback");
    if (fallback) fallback.remove();
    const exs = data;
    const checks = exs.map(crossCheck);
    const accChecks = exs.map(accCheck);
    const state = {
      cur: 0, view: "figure", folded: true, caseIdx: 2, texFolded: true,
      counts: exs.map((ex) => {
        const cs = { ...(ex.counts || {}) };
        for (const c of freeCounts(ex.skeleton.body)) if (!hasOwn(cs, c)) cs[c] = 3;
        return cs;
      }),
    };

    root.insertAdjacentHTML("beforeend", `<div class="sw-bar"></div><div class="sw-body"></div><div class="sw-foot"></div>`);
    const bar = root.querySelector(".sw-bar"), body = root.querySelector(".sw-body"), foot = root.querySelector(".sw-foot");

    function checkLine(k) {
      const c = checks[k], ex = exs[k];
      const exp = c.runs.filter((r) => !r.folded);
      const expOk = exp.filter((r) => r.ok);
      const foldOk = c.runs[0].ok;
      const ac = accChecks[k];
      const printOk = foldOk && expOk.length === exp.length && c.formulas.bad.length === 0;
      const allOk = printOk && (!ac || ac.ok);
      const sizes = exp.map((r) => countsText(r.counts)).join("; ");
      const accTxt = !ac ? ""
        : ac.ok ? ` Lean elaborated each of the ${ac.n} accessor paths that the transcript view shows at ${exp.length === 1 ? "this size" : "the first of these sizes"}${ac.cases > 1 ? ", in each of the " + ac.cases + " cases of the branch" : ""}, and the page computes the same ${ac.n}.`
        : ` The page's accessor paths differ from Lean's: ${ac.missing.length} of the page's paths were not elaborated by Lean${ac.missing.length ? " (" + ac.missing.join("; ") + ")" : ""}, and Lean elaborated ${ac.extra.length} that the page does not show${ac.extra.length ? " (" + ac.extra.join("; ") + ")" : ""}.`;
      const txt = printOk
        ? `${allOk ? "✓" : "✗"} On load, this page's port of Lean's printer reproduced, byte for byte, all ${c.formulas.ok} formula strings in the JSON, the folded figure, and the expanded figure at ${exp.length === 1 ? "" : exp.length + " sizes: "}${sizes}.${accTxt}`
        : `✗ The port disagrees with Lean: ${c.formulas.bad.length} formula strings, folded figure ${foldOk ? "equal" : "different"}, expanded figure equal at ${expOk.length} of ${exp.length} sizes. The figure below may not be Lean's.${accTxt}`;
      return `<span class="${allOk ? "sw-good" : "sw-bad"}" data-check="${allOk ? "ok" : "bad"}" data-example="${esc(ex.key)}">${esc(txt)}</span>`;
    }

    function countTools(k) {
      const cs = freeCounts(exs[k].skeleton.body);
      if (!cs.length) return "";
      return `<span class="sw-muted sw-small">Unroll with</span>` + cs.map((c) =>
        `<label class="sw-count">${math(c)} = <input type="number" min="0" max="${MAX_COUNT}" step="1" value="${state.counts[k][c]}" data-c="${esc(c)}" aria-label="value of ${esc(c)}"></label>`).join("");
    }
    function bindCounts(k) {
      body.querySelectorAll("input[data-c]").forEach((inp) => inp.addEventListener("change", () => {
        const v = Math.max(0, Math.min(MAX_COUNT, Math.round(+inp.value || 0)));
        state.counts[k][inp.dataset.c] = v;
        render();
        const again = body.querySelector(`input[data-c="${CSS.escape(inp.dataset.c)}"]`);
        if (again) again.focus();
      }));
    }
    function onSeg(sel, f) {
      const el = root.querySelector(sel);
      if (el) el.addEventListener("click", (e) => { const b = e.target.closest("button"); if (b) f(b.dataset.x); });
    }

    /* The LaTeX at the reader's counts: Lean's own string when Lean produced the figure at those
     * counts, the port's otherwise. */
    function texAt(k, folded) {
      const ex = exs[k];
      if (folded) return { tex: ex.tex, lean: true };
      const cs = state.counts[k];
      if (sameCounts(cs, ex.counts)) return { tex: ex.texExpanded, lean: true };
      const s = (ex.samples || []).find((x) => sameCounts(cs, x.counts));
      if (s) return { tex: s.tex, lean: true };
      return { tex: toTex(ex.title, false, walk(ex.skeleton, false, cs)), lean: false };
    }

    function render() {
      const k = state.cur, ex = exs[k], sk = ex.skeleton;
      bar.innerHTML = (exs.length > 1 ? seg("sw-pick", exs.map((e, i) => [String(i), e.short || e.title]), String(k), "Protocol") : `<span class="sw-title">${esc(ex.title)}</span>`) +
        seg("sw-views", VIEWS, state.view, "View");
      onSeg(".sw-pick", (x) => { state.cur = +x; render(); });
      onSeg(".sw-views", (x) => { state.view = x; render(); });
      const ck = checkLine(k);
      if (state.view === "figure") {
        const lines = walk(sk, state.folded, state.counts[k]);
        body.innerHTML = `<div class="sw-tools">${seg("sw-fold", [["1", "One generic round"], ["0", "Every round"]], state.folded ? "1" : "0", "Rounds")}${state.folded ? "" : countTools(k)}</div>` + figureHtml(lines);
        onSeg(".sw-fold", (x) => { state.folded = x === "1"; render(); });
        bindCounts(k);
        foot.innerHTML = legend + `<span>The figure is drawn by the same walk that prints the LaTeX view. "One generic round" prints each loop once over its round variable, as a paper does; "Every round" unrolls each loop with the counts you pick.</span>` + ck;
      } else if (state.view === "claims") {
        body.innerHTML = claimsHtml(sk);
        foot.innerHTML = `<span>Each stage declares its input and output claims as formulas. <code>Spec.inputProblem</code> and <code>Spec.outputProblem</code> are the languages these formulas denote, and the soundness and completeness statements in <code>Claims.lean</code> are about them. A green tag marks an input claim whose syntax tree equals the previous stage's output claim.</span>` + ck;
      } else if (state.view === "timeline") {
        const br = firstBranch(sk.body);
        const items = flatten(sk, state.caseIdx, state.counts[k]);
        const tools = (br ? `<span class="sw-muted sw-small">Branch case shown:</span>${seg("sw-case-pick", br.cases.map((c, i) => [String(i), `${br.on.base} = ${c.value}`]), String(Math.min(state.caseIdx, br.cases.length - 1)), "Branch case")}` : "") + countTools(k);
        body.innerHTML = (tools ? `<div class="sw-tools">${tools}</div>` : "") + timelineHtml(items);
        bindCounts(k);
        onSeg(".sw-case-pick", (x) => { state.caseIdx = +x; render(); });
        const det = body.querySelector(".sw-tl-detail");
        const show = (btn) => {
          body.querySelectorAll(".sw-tl-cell.sw-on").forEach((n) => n.classList.remove("sw-on"));
          btn.classList.add("sw-on");
          const it = items[+btn.dataset.i], n = it.n, md = { folded: false, env: it.env };
          let h;
          if (n.kind === "move") {
            const acc = accessorFor(items, +btn.dataset.i);
            const ty = acc.ok && ex.accessors && hasOwn(ex.accessors, acc.text) ? ex.accessors[acc.text] : null;
            const tyHtml = ty ? `<span class="sw-muted"> : </span><span class="sw-leanty" title="The type that Lean gave this path when the site was built">${esc(ty)}</span>`
              : acc.ok && it.ctx.some(isCase) ? " : Option _" : "";
            const note = acc.ok && ex.accessors && !ty
              ? `<div class="sw-small sw-muted">Lean elaborated the paths at the example's own sizes. Because this path is outside them, it has no type from Lean.</div>` : "";
            h = `<div class="sw-path${acc.ok ? "" : " sw-bad"}">${esc(acc.text)}${tyHtml}</div>${note}<div><b>${esc(n.owner)} ${esc(n.move)}</b> ${math(nameTex(md, n.name) + " \\in " + n.type)}${n.honest ? " · honest value " + annot(n.honest.text) : ""}</div>`;
          } else if (n.kind === "check") {
            h = `<div><b>check ${esc(n.label)}</b>, decided at the leaf</div><div>${math(synTex(md, n.formula.syntax))}</div>`;
          } else {
            h = `<div><b>let</b> ${math(nameTex(md, n.name) + " := " + synTex(md, n.formula.syntax))}</div>`;
          }
          det.innerHTML = h;
          typeset(det);
        };
        body.querySelectorAll("button.sw-tl-cell").forEach((b) => {
          b.addEventListener("mouseenter", () => show(b));
          b.addEventListener("focus", () => show(b));
          b.addEventListener("click", () => show(b));
        });
        const first = body.querySelector("button.sw-tl-cell");
        if (first) show(first);
        foot.innerHTML = legend + `<span>The transcript unrolls each loop with the count you pick. A move's accessor names the stages, loops, rounds and branch cases around it, then its label: the base of its name, or the base with its subscript when another move in the same context shares the base. The page applies Lean's matching rule (<code>Specs/Run.lean</code>). When the site was built, Lean elaborated each path at the example's own sizes on a transcript of the specification, and the type after a path is the type Lean gave it. Since Lean resolves a path while elaborating, an accessor needs a numeral count and a numeral round. Inside a branch the accessor returns an <code>Option</code>.</span>` + ck;
      } else if (state.view === "tex") {
        const t = texAt(k, state.texFolded);
        const portNote = state.texFolded ? "" : t.lean
          ? ""
          : ` Lean did not build the figure at these counts. This text therefore comes from the page's port of <code>Specs/Export.lean</code>.`;
        body.innerHTML = `<div class="sw-tools sw-spread"><span class="sw-tools">${seg("sw-tex-mode", [["1", "Folded"], ["0", "Expanded"]], state.texFolded ? "1" : "0", "LaTeX")}${state.texFolded ? "" : countTools(k)}</span><button type="button" class="sw-btn sw-copy">Copy</button></div><pre class="sw-src">${esc(t.tex)}</pre>`;
        onSeg(".sw-tex-mode", (x) => { state.texFolded = x === "1"; render(); });
        bindCounts(k);
        body.querySelector(".sw-copy").addEventListener("click", async (e) => {
          try { await navigator.clipboard.writeText(t.tex); e.target.textContent = "Copied"; }
          catch (_) {
            const r = document.createRange(); r.selectNodeContents(body.querySelector(".sw-src"));
            const s = getSelection(); s.removeAllRanges(); s.addRange(r); e.target.textContent = "Selected";
          }
        });
        foot.innerHTML = `<span>${t.lean ? `Lean's own output, computed by <code>Skel.toTex</code> when the site was built.` : ""}${portNote} The folded figure is the same for every count. <code>\\specannot</code> prints annotation in gray.</span>` + ck;
      } else {
        body.innerHTML = `<pre class="sw-src sw-json">${esc(JSON.stringify(sk, null, 1))}</pre>`;
        foot.innerHTML = `<span><code>Skel.toJson</code>, schema <code>${esc(sk.schema)}</code>, computed when the site was built. A loop is one node whose body is one generic round over its round variable and count symbol. Every formula carries its syntax tree and its folded TeX, and every annotation carries <code>"checked": false</code>.</span>` + ck;
      }
      typeset(body);
      typeset(foot);
      typeset(bar);
    }
    render();
    root.classList.add("sw-ready");
  }

  function mountAll() {
    document.querySelectorAll(".spec-widget").forEach(mount);
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", mountAll);
  else mountAll();

  /* For tests: the port, without the DOM. */
  window.specsiteProtocol = { walk, toTex, crossCheck, synTex, nameTex, flatten, accessorFor };
})();
