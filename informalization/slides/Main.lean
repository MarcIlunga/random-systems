/-
Copyright (c) 2026 Trail of Bits. Apache 2.0.
-/
import VersoSlides
import InformalizationSlides

open VersoSlides

/-- Build the deck, then post-process the HTML to follow de Moura's ETAPS look:
inject `custom.css`, set `disableLayout: true` (stops reveal.js' giant
auto-scaling), and inline the hover-docs JSON into the highlighting/panel scripts
so clickable Lean works when the file is opened directly (`file://`). -/
def main : IO UInt32 := do
  let config : Config :=
    { theme := "white", center := false, margin := 0,
      slideNumber := true, transition := "fade" }
  let rc ← slidesMain (config := config) (doc := %doc InformalizationSlides)
  let out := config.outputDir

  -- 1. custom stylesheet + Trail of Bits logo asset
  let css ← IO.FS.readFile "static/custom.css"
  IO.FS.writeFile (out / "custom.css") css
  for f in ["tob-logo.svg", "tob-logo-red.svg", "tob-logo-white.svg", "tob-wordmark.svg"] do
    let logo ← IO.FS.readFile ("static/" ++ f)
    IO.FS.writeFile (out / f) logo

  -- 2. patch index.html: link the css + disable reveal's layout auto-scaling
  let htmlPath := out / "index.html"
  let html ← IO.FS.readFile htmlPath
  let html := html.replace "</head>"
    "<link rel=\"stylesheet\" href=\"custom.css\">\n</head>"
  let html := html.replace "Reveal.initialize({"
    "Reveal.initialize({\n        disableLayout: true,"
  -- Informalization interactions, wired on load + Reveal ready (after KaTeX):
  --  • `.inf-toggle` ⊕ → unfold the `.inf-hidden` block in place (no slide advance)
  --  • `.inf-hover`  → tippy tooltip with the paired `.inf-goal` proof-state
  let deckJs :=
    "<script>function infWire(){" ++
    "document.querySelectorAll('.inf-toggle').forEach(function(t){if(t.dataset.w)return;t.dataset.w='1';" ++
    "t.addEventListener('click',function(e){e.stopPropagation();var s=t.closest('section');if(!s)return;" ++
    "s.querySelectorAll('.inf-hidden').forEach(function(h){h.classList.toggle('inf-show');});" ++
    "t.textContent=(t.textContent.trim()==='⊕')?'⊖':'⊕';});});" ++
    "document.querySelectorAll('.reveal section').forEach(function(s){" ++
    "var hs=s.querySelectorAll('.inf-hover'),gs=s.querySelectorAll('.inf-goal');" ++
    "hs.forEach(function(a,i){if(a.dataset.t)return;var g=gs[i];" ++
    "if(g&&window.tippy){a.dataset.t='1';tippy(a,{content:g.innerHTML,allowHTML:true,interactive:true,maxWidth:480,appendTo:document.body});g.style.display='none';}});});" ++
    "}window.addEventListener('load',function(){setTimeout(infWire,400);});" ++
    "if(window.Reveal&&Reveal.on){Reveal.on('ready',function(){setTimeout(infWire,400);});}" ++
    -- A fullscreen button → TRUE browser fullscreen (hides tabs/address bar; not
    -- macOS maximize). `F` also toggles via reveal.js.
    "(function(){var b=document.createElement('button');b.id='fsbtn';b.textContent='⛶';" ++
    "b.title='Fullscreen (F)';b.onclick=function(){" ++
    "if(document.fullscreenElement){document.exitFullscreen();return;}" ++
    "var el=document.documentElement;var rf=el.requestFullscreen||el.webkitRequestFullscreen||el.mozRequestFullScreen;" ++
    "if(rf){try{rf.call(el);}catch(e){}}};document.body.appendChild(b);})();" ++
    -- Trail of Bits brand mark: a small logo fixed top-right and bottom-right of
    -- every slide. It recolors itself (red on light slides, white on the dark
    -- ink title/section slides) via the `body.tob-dark-slide` class, toggled
    -- here whenever the active slide has the ink background color.
    "(function(){var mk=function(c){var d=document.createElement('div');" ++
    "d.className='tob-mark '+c;d.setAttribute('aria-label','Trail of Bits');" ++
    "document.body.appendChild(d);};mk('tob-mark-top');" ++
    "var sync=function(){var s=window.Reveal&&Reveal.getCurrentSlide?Reveal.getCurrentSlide():null;" ++
    "var dark=s&&s.getAttribute('data-background-color')==='#181717';" ++
    "document.body.classList.toggle('tob-dark-slide',!!dark);};" ++
    "if(window.Reveal&&Reveal.on){Reveal.on('ready',sync);Reveal.on('slidechanged',sync);}" ++
    "window.addEventListener('load',function(){setTimeout(sync,300);});})();" ++
    "</script>\n"
  let html := html.replace "</body>" (deckJs ++ "</body>")
  IO.FS.writeFile htmlPath html

  -- 3. inline the hover JSON so click/hover work from file:// (no fetch/CORS).
  --    One replacement of `fetch("-verso-docs.json")` with a resolved fake
  --    {ok, json} works for both highlighting.js and panel.js.
  let docsJsonPath := out / "-verso-docs.json"
  if ← docsJsonPath.pathExists then
    let docsJson ← IO.FS.readFile docsJsonPath
    let fake := "Promise.resolve({ok:true,json:function(){return " ++ docsJson ++ ";}})"
    for f in ["highlighting.js", "panel.js"] do
      let p := out / "lib" / f
      if ← p.pathExists then
        let js ← IO.FS.readFile p
        IO.FS.writeFile p (js.replace "fetch(\"-verso-docs.json\")" fake)

    -- Hover tooltips: highlighting.js wires them in `window.onload`, a single-
    -- assignment handler that never fires for a late-loaded script — so hover
    -- silently never initializes (the click panel uses Reveal's ready event and
    -- works). Rename the init and run it as soon as the DOM is ready.
    let hlPath := out / "lib" / "highlighting.js"
    if ← hlPath.pathExists then
      let hl ← IO.FS.readFile hlPath
      let hl := hl.replace "window.onload = async () => {" "window.__hlInit = async () => {"
      let runner :=
        "\n;(function(){var f=function(){if(window.__hlInit)window.__hlInit();};" ++
        "if(document.readyState!=='loading')f();" ++
        "else window.addEventListener('DOMContentLoaded',f);})();\n"
      IO.FS.writeFile hlPath (hl ++ runner)

  return rc
