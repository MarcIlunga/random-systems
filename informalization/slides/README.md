# Informalization slides — Verso presentation layer

The presentation media for informalization, built on **[VersoSlides](https://github.com/leanprover/verso-slides)**
(Verso's reveal.js genre — the same tool behind de Moura's
[ETAPS 2026 deck](https://leodemoura.github.io/static/etaps2026/)). This replaces
the earlier ad-hoc HTML/JS renderer: Lean code blocks are elaborated, syntax-
highlighted, and **clickable** (click a token → its proof state / info panel,
via Verso's tippy/popper panels), and our **informalized prose lives in the same
deck** beside the formal proof.

Separate from the `import Lean`-only core (`../Informalization/`): this project is
on Verso's toolchain (`v4.32.0-rc1`) and pulls Verso as a Lake dependency. The two
connect through the **`Explanation → Verso markup` bridge** (`../Informalization/VersoEmit.lean`).

## Files
- `InformalizationSlides.lean` — the deck (`#doc (Slides) …`): the missing arrow,
  `inj_comp` (clickable Lean + its informalization), CR18 Lemma 4.5 (verbatim-
  faithful informalization), the pipeline.
- `Main.lean` — `slidesMain` entry point.
- `lakefile.lean` / `lean-toolchain` — `require verso-slides`, toolchain v4.32.0-rc1.
- `_slides/` — the generated, self-contained output (open `_slides/index.html`).

## Build (needs network: fetches `verso-slides` + `verso` via Lake)
```sh
cd slides
lake build
lake exe «informalization-slides»     # writes _slides/index.html (offline, vendored reveal.js/KaTeX)
python3 -m http.server -d _slides      # then open http://localhost:8000
```
(Or just open the committed `_slides/index.html` directly — it is fully offline.)

## The bridge: Verso hosts the informalization text
`Explanation.toVerso` (in the core, pure, no Verso dep) emits VersoSlides markup
from any informalized `Explanation`:
- `math` → `` $`…` `` · `paragraph` → block · `indent` → `:::frame` ·
- `detail` / `clickable` / goal-state `tooltip` → `:::fragment` (Verso's
  click-reveal — the presentation analogue of show-hidden-detail).

The example command `#informalizeVerso <decl>` (`examples/Examples/InjCompVerso.lean`)
runs the full pipeline — `#informalize` → `FTL` → `Explanation` → `toVerso` —
and prints slide-ready markup. Paste it into a slide, or wire a build step to
splice it. The prose in `InformalizationSlides.lean` matches this generated output.

## Interaction (like de Moura's deck)
- Click a Lean token → info panel with its type / proof state.
- `-- ^ !click` / `-- !fragment` magic comments drive progressive proof reveals.
- Press `s` for speaker notes; arrows / space to navigate.
