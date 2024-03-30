---
title: Functor
date: 2023-08-30
tags: ["category theory", "haskell"]
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
<script id="dark-toggle" async src="/js/dark-toggle.js"></script>
</style>
{% endraw %}

<br>
<div class=typeclass>
<img src="/images/functor.svg">
</div>
<!-- The source as dot is next to image. Compile with: dot -Tsvg typeclasses.dot -o typeclasses.svg -->
<br>

A functor, in category theory, is a structural-preserving mapping between [categories](/category). Given two categories, $\mathcal{C}$ and $\mathcal{D}$, a functor $F: \mathcal{C} \rightarrow \mathcal{D}$ associates each object in $\mathcal{C}$ with an object in $\mathcal{D}$ and each morphism $f : A \rightarrow B$ in $\mathcal{C}$ with a morphism $F(f) : F(A) \rightarrow F(B)$ in $\mathcal{D}$, such that:

* $F(id_{A}) = id_{F(A)}$ for every object $A$ in $\mathcal{C}$,

* $F(g \circ f) = F(g) \circ F(f)$ for all morphisms $f : A \rightarrow B$ and $g : B \rightarrow C$ in $\mathcal{C}$

<!-- , or in terms of [hom-sets](/hom-sets) $Hom_{C}(A,B) \rightarrow Hom_{D}(F(A),F(B))$, -->


That is, functors must preserve identity morphisms and composition of morphisms. We can rephrase these conditions using the subsequent commutative diagram:
{% raw %}
\begin{xy}
\xymatrix{
F(A) \ar[r]_{F(f)} \ar@/^1.5pc/[rr]^{F(g\ \circ f)} & F(B) \ar[r]_{F(g)} & F(C) \\
A \ar[r]^{f} \ar@/_1.5pc/[rr]_{g\ \circ\ f} \ar[u]_{F} & B \ar[r]^{g} \ar[u]_{F} & C \ar[u]_{F}
}
\end{xy}
{% endraw %}

# Example

A Functor in Haskell is a typeclass that represents a type that can be mapped over, meaning that you can apply a function to every element of the type without changing its structure.

Haskell Definition of Functor (Interface)
{% vimhl hs %}
class Functor f where
    --      (A -> B) -> F(A) -> F(B)
    fmap :: (a -> b) -> f a  -> f b
{% endvimhl %}

The following condition must always hold:

{% vimhl hs %}
fmap id == id                   -- Identity
fmap (f . g) == fmap f . fmap g -- Composition
{% endvimhl %}

An Instance of Functor, the List Functor
{% vimhl hs %}
instance Functor [] where
    fmap = map
{% endvimhl %}

Another Instance, the Maybe Functor
{% vimhl hs %}
instance  Functor Maybe  where
    fmap _ Nothing       = Nothing
    fmap f (Just a)      = Just (f a)
{% endvimhl %}

All of the above is already implemented in the standard Haskell library, so you can simply open an interactive Haskell interpreter (ghci) and test the following examples.

{% vimhl hs %}
ghci> fmap (*2) [1,2,3]
[2,4,6]

ghci> fmap id [1,2,3]
[1,2,3]

ghci> fmap (++ "B") (Just "A")
Just "AB"

ghci> fmap (++ "B") Nothing
Nothing
{% endvimhl %}

Some more examples contains basically everything that can be mapped over:

* Either Functor: If the Either contains a right value, it applies the function to the value, else it leaves the left value untouched.
* IO Functor: Used to construct computations which perform I/O and computes a result.
* Future Functor: Applies a function to a value in a future (a sort of placeholder object for a value that is initially unknown).
* Const Functor: Ignores its function argument and always yields the same value.
* Identity Functor: Simply applies the given function to its argument without any additional behavior.
* Function Functor (in the sense of (a -> b) -> (c -> d)): Applies a function to the return type of another function.
* Tree Functor: Applies a function to every node in a tree.
* Pair Functor: Applies the function to the second element of a pair.
* Reader Functor: Applies a function to the result of another function (a "reader" of some shared environment)
* State Functor: Applies a function to the result of a stateful computation.
* Writer Functor: Applies a function to the result while preserving some additional logging or output.

### References

[^0]: The diagram displayed at the top of this post is a modified version of Brent Yorgey's [Typeclassopedia diagram](https://wiki.haskell.org/File:Typeclassopedia-diagram.png)
[^1]: [Functor in ncatlab](https://ncatlab.org/nlab/show/functor#definition)
