---
title: Applicative
date: 2023-08-31
tags: ["category theory", "abstract algebra"]
subtitle: A Lax Monoidal Endofunctor with Tensorial Strength
mathjax: true
---


<!-- subtitle: A Strong Lax Monoidal Functor -->

<!-- https://research-information.bris.ac.uk/ws/portalfiles/portal/177884475/algebra.pdf 15 -->

<!-- To minimize confusion, we use ‘lax monoidal functor with strength’ -->
<!-- to indicate the existence of tensorial strength, a broadcast operation of type A × F B → F (A × B), -->
<!-- and avoid the ambiguous term ‘strong lax monoidal functor’.) -->

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

A applicative, in category theory, is a categories.

<!-- Let $(\mathcal{C}, \otimes_{\mathcal{C}}, 1_{\mathcal{C}})$ and $(\mathcal{D}, \otimes_{\mathcal{D}}, 1_{\mathcal{D}})$ be two monoidal categories. A lax monoidal endofunctor between them is a functor $F : \mathcal{C} \rightarrow \mathcal{D}$ together with two coherence maps -->
Let $(\mathcal{C}, \otimes, 1_{\mathcal{C}})$ be a monoidal category. A lax monoidal endofunctor is a functor $F : \mathcal{C} \rightarrow \mathcal{C}$ together with two coherence maps:

<!-- * $\eta : 1_{\mathcal{D}} \rightarrow F(1_{\mathcal{C}})$ (called the unit morphism) -->
* $\eta : 1_{\mathcal{C}} \rightarrow F(1_{\mathcal{C}})$ (called the unit morphism)

* $\phi_{X,Y} : FX \otimes FY \rightarrow F(X \otimes Y)$ (a natural transformation)


Tensorial strength means that $\phi_{X,Y}$ is actually an isomorphism $FX \otimes FY \simeq F(X \otimes Y)$


<!-- , or in terms of [hom-sets](/hom-sets) $Hom_{C}(X,Y) \rightarrow Hom_{D}(F(X),F(Y))$, -->


such that the following diagrams commute:

https://arxiv.org/pdf/1406.4823.pdf 17


{% raw %}
\begin{xy}
\xymatrix{
(FX\ \otimes\ FY)\ \otimes\ FZ \ar[r]^{f} \ar[d]_{F} & FX\ \otimes\ (FY\ \otimes\ FZ) \ar[d]_{F} \\
F(X\ \otimes\ Y)\ \otimes\ FZ \ar[r]^{f} \ar[d]_{F} \ar[r]_{F(f)} \ar[d] & F(Y) \ar[d] \\
F((X\ \otimes\ Y)\ \otimes\ Z) \ar[r]_{F(f)} & F(Y) \\
}
\end{xy}
{% endraw %}

# Example

A Functor in Haskell is a typeclass that represents a type that can be mapped over, meaning that you can apply a function to every element of the type without changing its structure.

Haskell Definition of Functor (Interface)
{% vimhl hs %}
class (Functor f) => Applicative f where
    pure  :: a -> f a
    (<*>) :: f (a -> b) -> f a -> f b
{% endvimhl %}



{% vimhl hs %}

class Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

class Functor f => Monoidal f where
  unit :: f ()
  (**) :: f a -> f b -> f (a,b)
{% endvimhl %}

https://hackage.haskell.org/package/invertible-0.2.0.7/docs/Control-Invertible-Monoidal.html#t:Monoidal

https://wiki.haskell.org/Typeclassopedia#Alternative_formulation
(By the way, if you haven’t shown that join :: m (m a) -> m a for monads is equivalent to bind :: m a -> (a -> m b) -> m b, you should do that too.) The laws for this formulation are much nicer:

This is similar to the equivalent formulation of bind and >>= that we have shown in the post about monad.

```
-- unit ** v ≅ v - Left Identity.
-- u ** unit ≅ u - Right Identity.
-- u ** (v ** w) ≅ (u ** v) ** w - Associativity.
```

```
-- pure id <*> v = v - Identity.
-- pure f <*> pure x = pure (f x) - Homomorphism.
-- u <*> pure y = pure ($ y) <*> u - Interchange.
-- u <*> (v <*> w) = pure (.) <*> u <*> v <*> w - Composition.
```


```
-- F(X) ⊗ F(Y) -> F(X ⊗ Y)
-- mu :: (f a, f b) -> f (a, b)

(<*>) :: Monoidal f => f (a -> b) -> f a -> f b
 ff <*> fa = fmap (\(f,a) -> f a) (ff ** fa)
```

```
unit   = pure ()
f ** g = (,) <$> f <*> g

pure x  = const x <$> unit
f <*> g = uncurry ($) <$> (f ** g)
```


The following condition must always hold:

{% vimhl hs %}
pure id <*> v = v                            -- Identity
pure f <*> pure x = pure (f x)               -- Homomorphism
u <*> pure y = pure ($ y) <*> u              -- Interchange
pure (.) <*> u <*> v <*> w = u <*> (v <*> w) -- Composition
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

All of the above is already implemented in the standard Haskell library, so you can also simply open an interactive Haskell interpreter (ghci) and test the following examples.

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


[^1]: [Functor in ncatlab](https://ncatlab.org/nlab/show/functor#definition)
[^2]: [Typeclassopedia](https://wiki.haskell.org/Typeclassopedia)
