---
title: Profunctor Optics
date: 2023-06-23
tags: ["category theory"]
subtitle: Bidirectional Data Accessors
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


Imagine you have a complex data structure with many nested fields and subtypes. You want to access, modify, or replace some parts of it, but not all of it. You also want to preserve the structure and integrity of the data. How can you do that? One way is to use a powerful abstraction called a **profunctor optic**. A profunctor optic is a bidirectional data accessor that can capture common patterns of data transformation, such as accessing subfields or iterating over containers. You can also use different kinds of profunctor optics for different kinds of data. For example, you can use a **lens** to access and update a specific field of a record type, like the name of a person or the price of a product. You can use a **prism** to access and update one case of a sum type, like an error message or a success value. You can use a **traversal** to access and update multiple elements of a container type, like all the odd numbers in a list or all the keys in a map. The best thing about profunctor optics is that they are composable. You can combine them to access and update more complex parts of the data, like the email address of the first customer or the title of the last book. Profunctor optics make it easy and elegant to manipulate your data.

Now that you have some intuition let me introduce a more formal definition of profunctor optics. Let's say you have an enriched category $C$ with an endofunctor $F$ on $C$ and an adjunction $F \dashv U$ between $C$ and another category $D$. You want to define an action of $F$ on $D$ along $U$ that preserves some structure on both categories. One way is to use a sophisticated construction called a profunctor optic. A profunctor optic is an enriched natural transformation between two profunctors $P$ and $Q$ on $C \times D^{op}$ that satisfies some additional properties depending on the structure involved. You can also use different kinds of profunctor optics for different kinds of structures. For example, you can use a **lens** when $F$ is cartesian monoidal and preserves products, $P$ is $F \times Id_C$ and $Q$ is $Id_D \times U$; this corresponds to an action by Tambara modules on $C^{op} \times D^{op}$ along $U^{op} \times U^{op}$. You can use a **prism** when $F$ is cocartesian monoidal and preserves coproducts, $P$ is $Id_C + F$ and $Q$ is $Id_D + U$; this corresponds to an action by Tambara comodules on $C \times D$ along $U \times U$. You can use a **traversal** when $F$ is strong monoidal and preserves strength, $P$ is $F \otimes Id_C$ and $Q$ is $Id_D \otimes U$; this corresponds to an action by strong Tambara modules on $C^{op} \times D^{op}$ along $U^{op} \otimes U^{op}$. The best thing about profunctor optics is that they are categorical. You can compose them using whiskering and horizontal composition to obtain more general profunctor optics that correspond to more complex actions involving other structures such as monads, comonads, distributive laws, etc. Profunctor optics make it easy and rigorous to study data transformations in enriched categories!

I hope this helps you understand profunctor optics better. If you want to learn more, you can check out these references:


[^1]: [Profunctor Optics, a Categorical Update](https://arxiv.org/abs/2001.07488)
[^2]: [Profunctor Optics: The Categorical View](https://golem.ph.utexas.edu/category/2020/01/profunctor_optics_the_categori.html)
[^3]: [Practical Profunctor Lenses & Optics In PureScript](https://thomashoneyman.com/articles/practical-profunctor-lenses-optics/)
[^4]: [profunctor-optics: A compact optics library compatible with the typeclasses in profunctors](https://hackage.haskell.org/package/profunctor-optics)
