---
title: Monad
date: 2023-07-25
tags: ["category theory"]
subtitle: A Monoid in the Category of Endofunctors
mathjax: true
---


{% raw %}
<script>
  MathJax = {
    loader: {
      load: ['[custom]/xypic.js'],
      paths: {custom: 'https://cdn.jsdelivr.net/gh/sonoisa/XyJax-v3@3.0.1/build/'}
    },
    tex: {
      packages: {'[+]': ['xypic']}
    }
  };
</script>
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3.1.4/es5/tex-chtml-full.js"></script>
<!-- <script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3.1.4/es5/tex-svg-full.js"></script> -->

<script>
window.addEventListener('load', function() {
   document.querySelectorAll("mjx-xypic-object").forEach( (x) => (x.style.color = "var(--darkreader-text--text"));
   document.querySelectorAll("mjx-math > mjx-xypic > svg > g").forEach(x => x.setAttribute("stroke", "var(--darkreader-text--text"))
})
</script>


{% endraw %}

A Monad is a triple $(T, \eta, \mu)$ where $T: \mathcal{C} \rightarrow \mathcal{C}$ is an endofunctor, $\eta: 1_\mathcal{C} \rightarrow T$ is a natural transformation (the unit), and $\mu: TT \rightarrow T$ is another natural transformation (the multiplication). These must satisfy the following coherence conditions, known as the Monad laws:

* $\mu \circ T\mu = \mu \circ \mu T$ (associativity)
* $\mu \circ T\eta = \mu \circ \eta T = 1_T$ (left and right identity)

This means that for any object $X$ in $\mathcal{C}$, we have:

* $\mu_X \circ T(\mu_X) = \mu_X \circ \mu_{T(X)}$ (associativity)
* $\mu_X \circ T(\eta_X) = \mu_X \circ \eta_{T(X)} = id_{T(X)}$ (left and right unit laws)


We can rephrase these conditions using the subsequent commutative diagrams:

{% raw %}
<div class="splitscreen">
  <div class="left">
\begin{xy}
\xymatrix{
  TTT \ar[d]_{\mu T} \ar[r]^{T\mu} & TT \ar[d]^{\mu} \\
  TT \ar[r]_{\mu} & T
}
\end{xy}
  </div>

  <div class="right">
\begin{xy}
\xymatrix{
  T \ar[d]_{\eta T} \ar[r]^{T\eta} \ar@{=}[dr] & TT \ar[d]^{\mu} \\
  TT \ar[r]_{\mu} & T
}
\end{xy}
  </div>
</div>

{% endraw %}



This means that monads provide a way to express computations (in terms of morphisms) that include additional structure or side-effects (captured by the endofunctor $T$) in such a way that these computations can be chained together (via the $\mu$ natural transformation) and lifted over the monadic structure (via the $\eta$ natural transformation), and they do so in a way that is consistent (respecting the associativity and unit laws).


[^1]: [Monad in ncatlab](https://ncatlab.org/nlab/show/monad#definition)
