/-
Copyright (c) 2026 Trail of Bits. Apache 2.0.

Build target for the SwissCryptoDay talk deck.  Identical post-processing to
`Main.lean` (shared `static/custom.css`, Trail of Bits logos, informalization
JS), but renders `SwissCryptoDay` into its own output dir `_scd` so the demo
deck (`_slides`) is left untouched.
-/
import VersoSlides
import SwissCryptoDay

open VersoSlides

def main : IO UInt32 := do
  let config : Config :=
    { theme := "white", center := false, margin := 0,
      slideNumber := true, transition := "fade", outputDir := "_scd" }
  let rc ← slidesMain (config := config) (doc := %doc SwissCryptoDay)
  let out := config.outputDir

  -- 1. custom stylesheet + Trail of Bits logo assets
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
    "Reveal.initialize({\n        disableLayout: true,\n        fragmentInURL: true,"
  let deckJs :=
    "<script>function infWire(){" ++
    -- pair the i-th ⊕ in a slide with the i-th `.inf-hidden`, so each step
    -- unfolds independently (not all-at-once).
    "document.querySelectorAll('.reveal section').forEach(function(s){" ++
    "var tg=s.querySelectorAll('.inf-toggle'),hd=s.querySelectorAll('.inf-hidden');" ++
    "tg.forEach(function(t,i){if(t.dataset.w)return;t.dataset.w='1';" ++
    "t.addEventListener('click',function(e){e.stopPropagation();var h=hd[i];if(!h)return;" ++
    "h.classList.toggle('inf-show');" ++
    "t.textContent=h.classList.contains('inf-show')?'⊖':'⊕';});});});" ++
    "document.querySelectorAll('.reveal section').forEach(function(s){" ++
    "var hs=s.querySelectorAll('.inf-hover'),gs=s.querySelectorAll('.inf-goal');" ++
    "hs.forEach(function(a,i){if(a.dataset.t)return;var g=gs[i];" ++
    "if(g&&window.tippy){a.dataset.t='1';tippy(a,{content:g.innerHTML,allowHTML:true,interactive:true,maxWidth:480,appendTo:document.body});g.style.display='none';}});});" ++
    "}window.addEventListener('load',function(){setTimeout(infWire,400);});" ++
    "if(window.Reveal&&Reveal.on){Reveal.on('ready',function(){setTimeout(infWire,400);});}" ++
    "(function(){var b=document.createElement('button');b.id='fsbtn';b.textContent='⛶';" ++
    "b.title='Fullscreen (F)';b.onclick=function(){" ++
    "if(document.fullscreenElement){document.exitFullscreen();return;}" ++
    "var el=document.documentElement;var rf=el.requestFullscreen||el.webkitRequestFullscreen||el.mozRequestFullScreen;" ++
    "if(rf){try{rf.call(el);}catch(e){}}};document.body.appendChild(b);})();" ++
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
  let docsJsonPath := out / "-verso-docs.json"
  if ← docsJsonPath.pathExists then
    let docsJson ← IO.FS.readFile docsJsonPath
    let fake := "Promise.resolve({ok:true,json:function(){return " ++ docsJson ++ ";}})"
    for f in ["highlighting.js", "panel.js"] do
      let p := out / "lib" / f
      if ← p.pathExists then
        let js ← IO.FS.readFile p
        IO.FS.writeFile p (js.replace "fetch(\"-verso-docs.json\")" fake)
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
