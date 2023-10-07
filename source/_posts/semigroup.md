---
title: Semigroup
date: 2023-08-29
tags: ["category theory", "abstract algebra", "haskell"]
subtitle: An Associative Magma
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
<img src="/images/semigroup.svg" onclick="window.open(this.src)">
<!-- The source as dot is next to image. Compile with: dot -Tsvg typeclasses.dot -o typeclasses.svg -->
<br>



A semigroup is an algebraic structure $(S, \otimes)$ in which $S$ is a non-empty set and $\otimes : S \times S \rightarrow S$ is a binary associative operation on $S$, such that the equation $(a \otimes  b) \otimes c = a \otimes (b \otimes c)$ holds for all $a, b, c \in \mathcal{S}$. In category theory, a semigroup is a [monoid](/monoid/) where there might not be an identity element. More formally, a semigroup is a semicategory (a [category](/category) without the requirement for identiy morphism) $\mathcal{C}$ with just one object $S$ and the following conditions:

* The set of morphisms ([hom-set](/hom-set)) is closed under composition: For every pair of morphisms $f, g$ in $Hom_\mathcal{C}(S,S)$, their composition $f \circ g$ also belongs to $Hom_{C}(S,S)$

* The composition operation is associative: For any three morphisms $f, g, h$ in $Hom_{C}(S, S)$, we have $(f \circ g) \circ h = f \circ (g \circ h)$.

<!-- In other words, a semigroup is a single-object category where the morphisms follow the laws of a semigroup as defined in abstract algebra. T -->

<!-- |                | Closure | Associativity | Identity | Divisibility | Commutativity | -->
<!-- |----------------|---------|---------------|----------|--------------|:-------------:| -->
<!-- | Partial Magma  |         |               |          |              |               | -->
<!-- | Semigroupoid   |         | x             |          |              |               | -->
<!-- | Small Category |         | x             | x        |              |               | -->



# Example

A type qualifies as a Semigroup if it offers an associative function (<>), allowing the merging of any two type values into a single one.


Haskell Definition of Semigroup (Interface)
{% vimhl hs %}
class Semigroup a where
    -- ⊗  :  S x S  -> S (multiplication)
    (<>) :: a -> a -> a
{% endvimhl %}

Associativity implies that the following condition must always hold:

{% vimhl hs %}
(a <> b) <> c == a <> (b <> c)
{% endvimhl %}

An Instance of Semigroup, the List Semigroup
{% vimhl hs %}
instance Semigroup [a] where
    (<>) = (++)
{% endvimhl %}

Another Instance, the Maybe Semigroup
{% vimhl hs %}
instance Semigroup a => Semigroup (Maybe a) where
    Just a  <> Just b  = Just (a <> b)
    Just a  <> Nothing = Just a
    Nothing <> Just b  = Just b
    Nothing <> Nothing = Nothing
{% endvimhl %}

All of the above is already implemented in the standard Haskell library, so you can also simply open an interactive Haskell interpreter (ghci) and test the following examples.

{% vimhl hs %}
ghci> [1,2,3] <> [4,5,6]
[1,2,3,4,5,6]

ghci> Just "A" <> Just "B"
Just "AB"

ghci> Nothing <> Just "A" <> Nothing
Just "A"

ghci> Nothing <> Nothing
Nothing
{% endvimhl %}

Some more examples are:

* The naturals numbers without zero $({\mathbb  {N}},+)$ under addition. This forms a semigroup because addition is associative.

* The natural numbers $({\mathbb  {N}}_{0}, \times )$ under multiplication. This forms a semigroup because multiplication is associative, but is also a monoid $\left({\mathbb  {N}}_{0},\times,1\right)$ since 1 serves as the identity, as any number multiplied by 1 remains the same.

* Non-empty strings $(\texttt{String},++)$ under concatenation. This forms a semigroup because string concatenation is associative.

### References

[^0]: The diagram displayed at the top of this post is a modified version of Brent Yorgey's [Typeclassopedia diagram](https://wiki.haskell.org/File:Typeclassopedia-diagram.png)
[^1]: [Semigroups in ncatlab](https://ncatlab.org/nlab/show/semigroup#definition)
[^2]: [Semigroups and Monoids](https://boltje.math.ucsc.edu/courses/f15/f15m200notes.pdf)
