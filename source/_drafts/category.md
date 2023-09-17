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

<!-- A category $\mathcal{C}$ is a quadruple $(\text{Obj}(\mathcal{C}), \text{Mor}(\mathcal{C}),\mu,1_\mathcal{C})$ consisting of a collection of objects $\text{Obj}(\mathcal{C})$, -->
<!-- For each pair of objects $A,B$, a set $\text{Hom}(A,B)$ of morphisms, also called [hom-sets](/hom-sets). -->

<!-- composition is associative: for each quadruple $a,b,c,d \in \text{Obj}(\mathcal{C})$ of objects, if $f \in HOM\ Mor?$ -->

A category $\mathcal{C}$ consists of a collection of objects, denoted $\text{Obj}(\mathcal{C})$ and, for every two objects $x, y \in \text{Obj}(\mathcal{C})$, a set of morphisms $\text{Hom}(x,y)$, also called [hom-sets](/hom-sets), satisfying the following properties:

* For every three objects $x,y,z \in \text{Obj}(\mathcal{C})$, there is a composition law:

  * $\text{Hom}(y,z) \times \text{Hom}(x,y) \rightarrow \text{Hom}(x,z)$

* Composition is associative: for all $w,x,y,z \in \text{Obj}(\mathcal{C}), f \in \text{Hom}(y,z), g \in \text{Hom}(x,y), h \in \text{Hom}(w,x)$ we have:

    * $f \circ (g \circ h) = (f \circ g) \circ h$

* For each $x \in \text{Obj}(\mathcal{C})$, there is a unique element $1_{x} \in \text{Hom}(x,x)$ (identity morphism), such that, for every $y \in \text{Obj}(\mathcal{C})$, we have left and right unit laws:

    * $f \circ 1_{x} = f$ for all $f \in \text{Hom}(x, y)$
    * $1_{x} \circ f = f$ for all $f \in \text{Hom}(y,x)$

<!-- For each $x \in \text{Obj}(\mathcal{C})$, there is a unique element $1_{x} \in \text{Hom}(x,x)$ (identity morphism), such that for every pair $x,y \in \text{Obj}(\mathcal{C})$, if $f \in \text{Hom}(x,y)$, then we have left and right unit laws: -->

<!-- * $1_{y} \circ f = f = f \circ 1_{x}$ -->

It is common to express $x \in \mathcal{C}$ instead of $x \in \text{Obj}(\mathcal{C})$ and when indicating 'f is a function from x to y', it's typically written as $f: x \rightarrow y$ rather than $f \in \text{Hom}(x,y)$. A category is a very general concept, the objects and morphisms can be anything, as long as they adhere to the previously mentioned conditions. The following is an example category with a collection of objects $X, Y, Z$ and collection of morphisms denoted $f, g, g \circ f$, and the loops are the identity morphisms.

{% raw %}
\begin{xy}
	\xymatrix{
	X \ar@(l,u)^{1_X}[] \ar_{g\ \circ\ f}[dr] \ar^f[r] & Y \ar@(u,r)^{1_Y}[] \ar^g[d]\\
	&Z \ar@(d,r)_{1_Z}[]
	}
\end{xy}
{% endraw %}


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
