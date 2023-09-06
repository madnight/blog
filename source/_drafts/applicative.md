---
title: Applicative
date: 2023-08-31
tags: ["category theory", "haskell"]
subtitle: A Strong Lax Monoidal Endofunctor
mathjax: true
---


<!-- subtitle: A Lax Monoidal Endofunctor with Tensorial Strength -->


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
<img src="/images/applicative.png" onclick="window.open(this.src)">
<!-- The source as dot is next to image. Compile with: dot -Tsvg typeclasses.dot -o typeclasses.svg -->
<br>

An applicative, in category theory, can be seen as strong lax monoidal endofunctor. Let $(\mathcal{C}, \otimes, 1_{\mathcal{C}})$ be a monoidal category. A lax monoidal endofunctor is a functor $F : \mathcal{C} \rightarrow \mathcal{C}$ together with two coherence maps:
<!-- Let $(\mathcal{C}, \otimes_{\mathcal{C}}, 1_{\mathcal{C}})$ and $(\mathcal{D}, \otimes_{\mathcal{D}}, 1_{\mathcal{D}})$ be two monoidal categories. A lax monoidal endofunctor between them is a functor $F : \mathcal{C} \rightarrow \mathcal{D}$ together with two coherence maps -->

<!-- * $\eta : 1_{\mathcal{D}} \rightarrow F(1_{\mathcal{C}})$ (called the unit morphism) -->
* $\eta : 1_{\mathcal{C}} \rightarrow F(1_{\mathcal{C}})$ (the unit morphism)

* $\phi_{X,Y} : FX \otimes FY \rightarrow F(X \otimes Y)$ (a natural transformation)


<!-- Tensorial strength means that $\phi_{X,Y}$ is actually an isomorphism $FX \otimes FY \simeq F(X \otimes Y)$ -->

<!-- Within the framework of category theory, the notion of monoidal structure preservation connects to the concept of tensorial strength, thus a strong lax monoidal functor is another term for an applicative functor. Nonetheless, in Haskell, it is inherent that every functor possesses unambiguous strength in relation to the product. -->

<!-- , or in terms of [hom-sets](/hom-sets) $Hom_{C}(X,Y) \rightarrow Hom_{D}(F(X),F(Y))$, -->


such that the following diagrams commute:

<!-- https://arxiv.org/pdf/1406.4823.pdf 17 (strength}) -->

<!-- https://en.wikipedia.org/wiki/Monoidal_functor -->

<!-- https://openaccess.city.ac.uk/id/eprint/1141/1/ 7 -->

{% raw %}
\begin{xy}
\xymatrix{
(FX\ \otimes\ FY)\ \otimes\ FZ \ar[r]^{\alpha} \ar[d]_{\phi_{X,Y}\ \otimes\ FZ} & FX\ \otimes\ (FY\ \otimes\ FZ) \ar[d]^{FX\ \otimes\ \phi_{Y,Z}} \\
F(X\ \otimes\ Y)\ \otimes\ FZ \ar[d]_{\phi_{X\ \otimes\ Y,Z}} & FX\ \otimes\ F(Y\ \otimes\ Z) \ar[d]^{\phi_{X,Y\ \otimes\ Z}} \\
F((X\ \otimes\ Y)\ \otimes\ Z) \ar[r]_{F_{\alpha}} & F(X\ \otimes\ (Y\ \otimes\ Z)) \\
}
\end{xy}
{% endraw %}

{% raw %}
<div class="splitscreen">
  <div class="left">
\begin{xy}
\xymatrix{
  FX\ \otimes\ 1_{\mathcal{C}}\ar[d]_{\rho} \ar[r]^{FX\ \otimes\ \eta\ \ \ \ \ } & FX\ \otimes\ F(1_{\mathcal{C}}) \ar[d]^{\phi_{X,1_{\mathcal{C}}}} \\
  FX & F(X\ \otimes\ 1_{\mathcal{C}}) \ar[l]_{F_{\rho}}
}
\end{xy}
  </div>

  <div class="right">
\begin{xy}
\xymatrix{
  1_{\mathcal{C}}\ \otimes\ FY\ar[d]_{\lambda} \ar[r]^{\eta\ \otimes\ FY\ \ \ \ } & F(1_{\mathcal{C}})\ \otimes\ F\ Y \ar[d]^{\phi_{1_{\mathcal{C},Y}}} \\
  FY & F(1_{\mathcal{C}}\ \otimes\ Y) \ar[l]_{{F_{\lambda}}}
}
\end{xy}
  </div>
</div>
{% endraw %}

The different natural transformations, indicated by $\alpha$ (associativity) ,$\rho$ (right identity) ,$\lambda$ (left identity) are part of the monoidal structure on ${\mathcal {C}}$.

Every functor applied to the monoidal category $\mathbf{Set}$, with the tensor product replaced by cartesian product, inherently possesses a unique strength, resulting in every functor within $\mathbf{Set}$ being strong. In simpler terms, a strong lax monoidal functor is just a lax monoidal functor that also has the property of being a strong functor, and its strength coherently associates with the monoidal structure. When we apply this in the context of $\mathbf{Set}$ functors, this coherent association is automatically provided. [^3]


# Example


The Applicative Typeclass is Haskell looks slightly different then our definition of a lax monidal functor. However there is another typeclass in Haskell called monoidal that directly reflects our definition. Moreover, there is a equivalence between the two typeclasses Applicative and Monoidal. This is similar to the equivalent formulation of bind and >>= that we have shown in the post about [monad](/monad). Let me first introduce the typeclass Monoidal and then we show that this is equivalent to Applicative.


Haskell Definition of Monoidal (Interface)

{% vimhl hs %}
class Functor f => Monoidal f where
  unit :: f ()
  (**) :: f a  -> f b  -> f (a, b)
{% endvimhl %}

Please note that `fa -> fb -> f(a, b)` is actually the curried version of
`(f a, f b) -> f (a, b)`

{% vimhl hs %}
curry :: ((a, b) -> c) -> a -> b -> c
curry f x y = f (x, y)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f p =  f (fst p) (snd p)
{% endvimhl %}

Haskell comes with curry and uncurry as part of its standard library, which together form an isomorphism. Hence we can also phrase Monoidal in this way, and it aligns seamlessly with our categorical definition of a strong lax monoidal functor.

{% vimhl hs %}
class Functor f => Monoidal f where
-- η     : 1  -> F(1) (unit)
  unit' :: () -> f ()
-- ϕx,y  : F(X) ⊗ F(Y) -> F(X ⊗ Y)
  (**') :: (f a, f b)   -> f (a, b)
{% endvimhl %}


We have the usual monoidal laws:

{% vimhl hs %}
unit ** v == v == v ** unit    -- Left and Right Identity
u ** (v ** w) == (u ** v) ** w -- Associativity
{% endvimhl %}


Now that we have established the Definition lets have a look at the equivalent Applicative definition in Haskell:

Haskell Definition of Applicative (Interface)

{% vimhl hs %}
class Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
{% endvimhl %}



This is how to recover Applicative in terms of Monoidal
```
pure :: Monoidal f => a -> f a
pure x  = fmap (const x) unit

(<*>) :: Monoidal f => f (a -> b) -> f a -> f b
f <*> g = fmap uncurry ($) (f ** g)
```

And this is how to get Monoidal in terms of Applicative:

```
Applicative f => f ()
unit   = pure ()

(**) :: Applicative f => f a  -> f b  -> f (a, b)
f ** g = fmap (,) f <*> g
```

We have now established and forward and backward translation between Applicative and Monoidal, hence they are isomorphic. This equality between Applicative and Monoidal has actually be shown in a computer checked [proof](https://stackoverflow.com/a/62959880) in Coq.

<!-- Require Import Coq.Program.Basics. -->
<!-- Require Import Coq.Init.Datatypes. -->
<!-- Require Import Coq.Init.Notations. -->

<!-- Notation "f ∘ g" := (compose f g). -->

<!-- Class Functor (F: Type -> Type) : Type := -->
<!--   { fmap : forall {x} {y}, (x->y) -> (F x->F y) -->
<!--   ; fmap_id : forall x, @fmap x x id = id -->
<!--   ; fmap_compose : forall {x} {y} {z} (f: y->z) (g: x->y) -->
<!--                      , fmap (f∘g) = fmap f ∘ fmap g -->
<!--   }. -->

<!-- Lemma fmap_twice {F} `{Functor F} {x} {y} {z} (f: y->z) (g: x->y) (xs: F x) -->
<!--                      : fmap (f∘g) xs = fmap f (fmap g xs). -->
<!-- Proof. -->
<!--   rewrite fmap_compose. now compute. -->
<!-- Qed. -->

<!-- Definition parallel {a} {b} {c} {d} (f: a->c) (g: b->d) -->
<!--   : (a*b) -> (c*d) := fun xy => match xy with -->
<!--                                 | (x,y) => (f x, g y) -->
<!--                                 end. -->

<!-- Notation "f *** g" := (parallel f g) (at level 40, left associativity). -->

<!-- Definition rassoc {a} {b} {c} : ((a*b)*c) -> (a*(b*c)) -->
<!--     := fun xyz => match xyz with | ((x,y),z) => (x,(y,z)) end. -->

<!-- Definition tt_ {a} (x:a) := (tt, x). -->
<!-- Definition _tt {a} (x:a) := (x, tt). -->

<!-- Class Monoidal F `{Functor F} : Type := -->
<!--   { funit : F unit -->
<!--   ; fzip : forall {a} {b}, F a -> F b -> F (a*b) -->
<!--   ; left_identity : forall {a} (v: F a) -->
<!--            , fzip funit v = fmap tt_ v -->
<!--   ; right_identity : forall {a} (v: F a) -->
<!--            , fzip v funit = fmap _tt v -->
<!--   ; associativity : forall {a} {b} {c} (u: F a) (v: F b) (w: F c) -->
<!--            , fzip u (fzip v w) = fmap rassoc (fzip (fzip u v) w) -->
<!--   ; naturality : forall {a} {b} {c} {d} -->
<!--                         (g: a->c) (h: b->d) (u: F a) (v: F b) -->
<!--            , fmap (g***h) (fzip u v) = fzip (fmap g u) (fmap h v) -->
<!--   }. -->

<!-- Notation "u ** v" := (fzip u v) (at level 40, left associativity). -->

<!-- Lemma naturalityL {F} `{Monoidal F} {a} {b} {c} -->
<!--                            (f: a->c) (u: F a) (v: F b) -->
<!--            : fmap (f***id) (fzip u v) = fzip (fmap f u) v. -->
<!-- Proof. -->
<!--   assert (v = fmap id v) as ->. { now rewrite fmap_id. } -->
<!--   rewrite <- naturality. -->
<!--   assert (v = fmap id v) as <-. { now rewrite fmap_id. } -->
<!--   now trivial. -->
<!-- Qed. -->
<!-- Lemma naturalityR {F} `{Monoidal F} {a} {b} {c} -->
<!--                            (f: b->c) (u: F a) (v: F b) -->
<!--            : fmap (id***f) (fzip u v) = fzip u (fmap f v). -->
<!-- Proof. -->
<!--   assert (u = fmap id u) as ->. { now rewrite fmap_id. } -->
<!--   rewrite <- naturality. -->
<!--   assert (u = fmap id u) as <-. { now rewrite fmap_id. } -->
<!--   now trivial. -->
<!-- Qed. -->

<!-- Definition to {a} {b} (y: a) (f: a->b) := f y. -->

<!-- Class Applicative F `{Functor F} : Type := -->
<!--   { pure : forall {a}, a -> F a -->
<!--   ; app : forall {a} {b}, F (a->b) -> F a -> F b -->
<!--   ; identity : forall {a} (v: F a) -->
<!--               , app (pure id) v = v -->
<!--   ; homomorphism : forall {a} {b} (f: a->b) (x: a) -->
<!--               , app (pure f) (pure x) = pure (f x) -->
<!--   ; interchange : forall {a} {b} (u: F (a->b)) (y: a) -->
<!--               , app u (pure y) = app (pure (to y)) u -->
<!--   ; composition : forall {a} {b} {c} -->
<!--                          (u: F (b->c)) (v: F (a->b)) (w: F a) -->
<!--               , app u (app v w) = app (app (app (pure compose) u) v) w -->
<!--   ; appFtor : forall {a} {b} (g: a->b) (x: F a) -->
<!--               , fmap g x = app (pure g) x -->
<!--   }. -->

<!-- Notation "fs <*> xs" := (app fs xs) (at level 40, left associativity). -->

<!-- Require Import Coq.Program.Tactics. -->
<!-- Require Import Coq.Logic.FunctionalExtensionality. -->

<!-- Definition apl {a} {b} (fx: (a->b)*a) -->
<!--    := match fx with |(f,x) => f x end. -->

<!-- Program Instance MonoidalIsApplicative {F} `{Monoidal F} -->
<!--     : Applicative F -->
<!--   := { pure := fun {a} (x: a) => fmap (const x) funit -->
<!--      ; app := fun {a} {b} (fs: F (a->b)) (xs: F a) -->
<!--               => fmap apl (fzip fs xs) }. -->
<!-- Next Obligation. (* identity *) -->
<!--   rewrite <- naturalityL. -->
<!--   rewrite -> left_identity. -->
<!--   repeat (rewrite <- fmap_twice). -->
<!--   rewrite -> fmap_id. -->
<!--   now compute. -->
<!-- Qed. -->
<!-- Next Obligation. (* homomorphism *) -->
<!--   rewrite <- naturality. -->
<!--   rewrite -> left_identity. -->
<!--   repeat (rewrite <- fmap_twice). -->
<!--   now compute. -->
<!-- Qed. -->
<!-- Next Obligation. (* interchange *) -->
<!--   rewrite <- naturalityL. -->
<!--   rewrite <- naturalityR. -->
<!--   repeat (rewrite <- fmap_twice). -->
<!--   rewrite -> right_identity. -->
<!--   rewrite -> left_identity. -->
<!--   repeat (rewrite <- fmap_twice). -->
<!--   now compute. -->
<!-- Qed. -->
<!-- Next Obligation. (* composition *) -->
<!--   rewrite <- naturalityR. -->
<!--   rewrite -> associativity. -->
<!--   repeat (rewrite <- naturalityL). -->
<!--   rewrite -> left_identity. -->
<!--   repeat (rewrite <- naturalityL). -->
<!--   repeat (rewrite <- fmap_twice). -->

<!--   f_equal.                      (*    This part is just about *) -->
<!--   unfold compose.                 (*  convincing Coq that two  *) -->
<!--   apply functional_extensionality. (* functions are equal, it  *) -->
<!--   intro x.                         (* has nothing to do with   *) -->
<!--   destruct x as ((btc, atb), a0). (*  applicative or monoidal  *) -->
<!--   now compute.                  (*    functors, specifically. *) -->
<!-- Qed. -->
<!-- Next Obligation. (* appFtor *) -->
<!--   rewrite <- naturalityL. -->
<!--   rewrite -> left_identity. -->
<!--   repeat (rewrite <- fmap_twice). -->
<!--   now compute. -->
<!-- Qed. -->


<!-- Lemma fmapPure {F} `{Applicative F} {a} {b} -->
<!--         (f: a->b) (x: a) : fmap f (pure x: F a) = pure (f x). -->
<!-- Proof. -->
<!--   rewrite -> appFtor. -->
<!--   now apply homomorphism. -->
<!-- Qed. -->

<!-- Lemma fmapBracket {F} `{Applicative F} {a} {b} {c} {d} -->
<!--       (f: c->d) (g: a->b->c) (xs: F a) (ys: F b) -->
<!--      : fmap f (fmap g xs<*>ys) = fmap (fun x y => f (g x y)) xs <*> ys. -->
<!-- Proof. -->
<!--   repeat (rewrite -> appFtor). -->
<!--   rewrite -> composition. -->
<!--   rewrite -> homomorphism. -->
<!--   rewrite -> composition. -->
<!--   repeat (rewrite -> homomorphism). -->
<!--   now compute. -->
<!-- Qed. -->

<!-- Lemma fmap_both {F} `{Applicative F} {a} {b} {c} {d} -->
<!--       (f: a->c->d) (g: b->c) (xs: F a) (ys: F b) -->
<!--      : fmap f xs <*> fmap g ys = fmap (fun x y => f x (g y)) xs <*> ys. -->
<!-- Proof. -->
<!--   repeat (rewrite -> appFtor). -->
<!--   rewrite -> composition. -->
<!--   repeat (rewrite <- appFtor). -->
<!--   rewrite <- fmap_twice. -->
<!--   rewrite -> interchange. -->
<!--   rewrite -> appFtor. -->
<!--   rewrite -> composition. -->
<!--   repeat (rewrite -> homomorphism). -->
<!--   rewrite <- appFtor. -->
<!--   now compute. -->
<!-- Qed. -->

<!-- Definition tup {a} {b} (x:a) (y:b) : (a*b) := (x,y). -->

<!-- Program Instance ApplicativeIsMonoidal {F} `{Applicative F} -->
<!--     : Monoidal F -->
<!--   := { funit := pure tt -->
<!--      ; fzip := fun {a} {b} (u: F a) (v: F b) -->
<!--                    => fmap tup u <*> v }. -->
<!-- Next Obligation. (* left_identity *) -->
<!--   repeat (rewrite -> appFtor). -->
<!--   rewrite -> homomorphism. -->
<!--   now compute. -->
<!-- Qed. -->
<!-- Next Obligation. (* right_identity *) -->
<!--   repeat (rewrite -> appFtor). -->
<!--   rewrite -> interchange. -->
<!--   rewrite -> composition. -->
<!--   repeat (rewrite -> homomorphism). -->
<!--   now compute. -->
<!-- Qed. -->
<!-- Next Obligation. (* associativity *) -->
<!--   repeat (rewrite -> fmapBracket). -->
<!--   rewrite -> composition. -->
<!--   repeat (rewrite <- appFtor). -->
<!--   rewrite <- fmap_twice. -->
<!--   rewrite -> fmap_both. -->
<!--   now compute. -->
<!-- Qed. -->
<!-- Next Obligation. (* naturality *) -->
<!--   rewrite -> fmap_both. -->
<!--   rewrite <- fmap_twice. -->
<!--   rewrite -> fmapBracket. -->
<!--   now compute. -->
<!-- Qed. -->

<!-- Compiled with Coq 8.9.1. -->


<!-- ``` -->
<!-- -- pure id <*> v == v == v <*> pure id -- Left and Right Identity -->
<!-- -- u <*> (v <*> w) = pure (.) <*> u <*> v <*> w --- Composition. -->
<!-- ``` -->



<!-- The following condition must always hold: -->

<!-- {% vimhl hs %} -->
<!-- pure id <*> v = v                            -- Identity -->
<!-- pure f <*> pure x = pure (f x)               -- Homomorphism -->
<!-- u <*> pure y = pure ($ y) <*> u              -- Interchange -->
<!-- pure (.) <*> u <*> v <*> w = u <*> (v <*> w) -- Composition -->
<!-- {% endvimhl %} -->

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
[^3]: [Notions of Computation as Monoids](https://arxiv.org/pdf/1406.4823.pdf)
