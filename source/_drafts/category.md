---
title: Category
date: 2023-09-14
tags: ["category theory", "haskell"]
subtitle: Collection of Objects Linked by Arrows
mathjax: true
---


{% raw %}
<script>
  MathJax = {
    loader: {
      load: ['[custom]/xypic.js'],
      paths: {custom: 'https://beuke.org/js'}
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

</style>
{% endraw %}

<br>
<img src="/images/functor.svg" onclick="window.open(this.src)">
<!-- The source as dot is next to image. Compile with: dot -Tsvg typeclasses.dot -o typeclasses.svg -->
<br>

A category $\mathcal{C}$ is a quadruple $(\text{Obj}(\mathcal{C}), \text{Mor}(\mathcal{C}),\mu,1_\mathcal{C})$ consisting of a collection of objects $\text{Obj}(\mathcal{C})$,
For each pair of objects $A,B$, a set $\text{Hom}(A,B)$ of morphisms, also called [hom-sets](/hom-sets).

* Set, the category of sets and set functions
* Mon, the category of monoids and monoid morphisms
* Monoids are themselves one-object categories
* Grp, the category of groups and group morphisms
* Rng, the category of rings and ring morphisms
* Grph, the category of graphs and graph morphisms
* Top, the category of topological spaces and continuous maps
* Preord, the category of preorders and order preserving maps
* CPO, the category of complete partial orders and continuous functions
* Cat, the category of categories and functors
* The category of data types and functions on data structures
* The category of functions and data flows (data flow diagram)
* The category of stateful objects and dependencies (object diagram)
* The category of values and value constructors
* The category of states and messages (state diagram)

### References

[^0]: The diagram displayed at the top of this post is a modified version of Brent Yorgey's [Typeclassopedia diagram](https://wiki.haskell.org/File:Typeclassopedia-diagram.png)
