---
title: Functor
date: 2023-08-30
tags: ["category theory", "abstract algebra"]
subtitle: A Homomorphism of Categories
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

A functor, in category theory, is a structural-preserving of mapping between categories. Given two categories, $\mathcal{C}$ and $\mathcal{D}$, a functor $F: \mathcal{C} \rightarrow \mathcal{D}$ associates each object in $\mathcal{C}$ with an object in $\mathcal{D}$ and each morphism $f : X \rightarrow Y$ in $\mathcal{C}$ with a morphism $F(f) : F(X) \rightarrow F(Y)$ in $\mathcal{D}$, such that:

* $F(id_{X}) = id_{F(X)}$ for every object $X$ in $\mathcal{C}$,
* $F(g \circ f) = F(g) \circ F(f)$ for all morphisms $f : X \rightarrow Y$ and $g : Y \rightarrow Z$ in $\mathcal{C}$


That is, functors must preserve identity morphisms and composition of morphisms.


We can rephrase these conditions using the subsequent commutative diagrams:

{% raw %}
\begin{xy}
\xymatrix{
F(X) \ar[r]_{F(f)} \ar@/^1.5pc/[rr]^{F(g\ \circ f)} & F(Y) \ar[r]_{F(g)} & F(Z) \\
X \ar[r]^{f} \ar@/_1.5pc/[rr]_{g\ \circ\ f} \ar[u]_{F} & Y \ar[r]^{g} \ar[u]_{F} & Z \ar[u]_{F}
}
\end{xy}
{% endraw %}




# Example

A type qualifies as a Semigroup if it offers an associative function (<>), allowing the merging of any two type values into a single one.


Haskell Definition of Semigroup (Interface)
{% vimhl hs %}
class Semigroup a where
 -- ⊗ :  S x S  -> S (multiplication)
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


[^1]: [Semigroups in ncatlab](https://ncatlab.org/nlab/show/semigroup#definition)
[^2]: [Typeclassopedia](https://wiki.haskell.org/Typeclassopedia)
[^4]: [Semigroups and Monoids](https://boltje.math.ucsc.edu/courses/f15/f15m200notes.pdf)
