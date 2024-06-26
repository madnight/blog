---
title: Monoid
date: 2023-08-27
tags: ["category theory", "abstract algebra"]
subtitle: A Semigroup with Identity
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

<script id="MathJax-script" src="https://cdn.jsdelivr.net/npm/mathjax@3.1.4/es5/tex-chtml-full.js"></script>
<script id="dark-toggle" src="/js/dark-toggle.js"></script>

</style>
{% endraw %}

<br>

<div class=typeclass>
<img src="/images/monoid.svg" onclick="window.open(this.src)">
</div>
<!-- The source as dot is next to image. Compile with: dot -Tsvg typeclasses.dot -o typeclasses.svg -->
<br>

In category theory, a Monoid is a triple ($M$, $\eta$, $\mu$) in a monoidal [category](/category) ($\mathcal{C}$, $\otimes$, $1_{M}$) together with two morphisms:

* $\eta: 1_{M} \rightarrow M$ is a [natural transformation](/natural-transformation) (the unit)
* $\mu: M \otimes M \rightarrow M$ is another natural transformation (the multiplication)

These must satisfy the following coherence conditions:

* $\mu(\mu(a, b), c) = \mu(a, \mu(b, c))\ \ \forall\ a, b, c \in M$ (associativity)
* $\mu(\eta(1_{M}), a) = a = \mu(a, \eta(1_{M}))\ \ \forall\ a \in M$ (left and right identiy)

We can rephrase these conditions using the subsequent commutative diagrams:

{% raw %}
<div class="splitscreen">
  <div class="left">
\begin{xy}
\xymatrix{
  M\ \otimes\ M\ \otimes\ M \ar[d]_{\mu M} \ar[r]^{M\mu} & M\ \otimes\ M \ar[d]^{\mu} \\
  M\ \otimes\ M \ar[r]_{\mu} & M
}
\end{xy}
  </div>
  <div class="right">
\begin{xy}
\xymatrix{
  M \ar[d]_{\eta M} \ar[r]^{M\eta} \ar@{=}[dr] & M\ \otimes\ M \ar[d]^{\mu} \\
  M\ \otimes\ M \ar[r]_{\mu} & M
}
\end{xy}
  </div>
</div>
{% endraw %}

Monoids are a powerful abstraction that can be used to solve a wide variety of problems. Monoids are becoming increasingly important in computer science because they provide a versatile framework for combining elements, especially in the context of parallel and distributed computing. For example, if you need to combine values in a way that's associative and has an identity, you can model your problem as a monoid.

Consider using monoids for aggregations on large data sets. Because of the associative property, the operation can occur in any order and still yield the same result, enabling parallel processing. The identity element provides a starting value for this computation. The classic examples of this are sum and multiplication on numbers, but also concatenation on strings or lists and more. Monoids are also used in the design of compilers and interpreters. For example, the abstract syntax tree of a program can be represented as a monoid.

# Example


The Monoid, by definition, requires us to implement two functions: the unit, which is called *mempty* in Haskell, where we have to provide a neutral element, and the multiplication `<>` (*mappend*).

Haskell Definition of Monoid (Interface)
{% vimhl hs %}
class Monoid a where
  -- η : 1 -> M (unit)
    mempty  :: a

  -- μ : M x M -> M (multiplication)
    mappend :: a -> a -> a
{% endvimhl %}

These have to obey the Monoid laws (<> infix notation for *mappend*) in pseudo notation:
{% vimhl hs %}
(x <> y) <> z = x <> (y <> z) -- associativity
mempty <> x <> mempty = x     -- left and right identity
{% endvimhl %}

An Instance of Monoid, the List Monoid
{% vimhl hs %}
instance Monoid [a] where
    mempty  = []
    mappend = (++)

{% endvimhl %}

Another Instance, the Maybe Monoid
{% vimhl hs %}
instance Monoid a => Monoid (Maybe a) where
    mempty = Nothing
    Just a  <> Just b  = Just (a <> b)
    Just a  <> Nothing = Just a
    Nothing <> Just b  = Just b
    Nothing <> Nothing = Nothing
{% endvimhl %}

All of the above is already implemented in the standard Haskell library, so you can also simply open an interactive Haskell interpreter (ghci) and test the following examples.
{% vimhl hs %}
ghci> mappend [1,2,3] [4,5,6]
[1,2,3,4,5,6]

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

* The naturals numbers $\left({\mathbb  {N}}_{0},+,0\right)$ under addition. This forms a monoid because addition is associative, and 0 serves as the identity, as any number added by 0 remains the same.

* The natural numbers $\left({\mathbb  {N}}_{0},\times,0\right)$ under multiplication. This forms a monoid because multiplication is associative, and 1 serves as the identity, as any number multiplied by 1 remains the same.

* Strings $(\texttt{String},++,\texttt{""})$ under concatenation. This forms a monoid because string concatenation is associative, and the empty string $\texttt{""}$ serves as the identity, as any string concatenated with $\texttt{""}$ remains the same.

### References

[^0]: The diagram displayed at the top of this post is a modified version of Brent Yorgey's [Typeclassopedia diagram](https://wiki.haskell.org/File:Typeclassopedia-diagram.png)
[^1]: [Monoids in ncatlab](https://ncatlab.org/nlab/show/monoids#definition)
[^2]: [Monoids in Haskell](https://en.wikibooks.org/wiki/Haskell/Monoids)
