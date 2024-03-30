document.addEventListener('DOMContentLoaded', (event) => {

// Code to run after MathJax has finished loading and rendering goes here
MathJax.startup.promise.then(function() {
   const rootStyles = getComputedStyle(document.documentElement);
   const textVarValue = rootStyles.getPropertyValue('--svg-text').trim();
   document.querySelectorAll("mjx-xypic-object").forEach( (x) => (x.style.color = textVarValue));
   document.querySelectorAll("mjx-math > mjx-xypic > svg > g").forEach(x => x.setAttribute("stroke", textVarValue));
});
})

window.matchMedia('(prefers-color-scheme: dark)').addListener(e => {
  const textVarValue = getComputedStyle(document.documentElement).getPropertyValue('--svg-text').trim();
   document.querySelectorAll("mjx-xypic-object").forEach( (x) => (x.style.color = textVarValue));
   document.querySelectorAll("mjx-math > mjx-xypic > svg > g").forEach(x => x.setAttribute("stroke", textVarValue));
});
