---
title: Natural Transformation
date: 2023-09-10
tags: ["category theory", "haskell"]
subtitle: A Morphism of Functors
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

Let $\mathcal{C}$ and $\mathcal{D}$ be categories and $F$ and $G$ be Functors $\mathcal{C} \rightarrow \mathcal{D}$. Then a natrual transofrmation $\alpha$ from $F$ to $G$ is a family of morphism that satisfies the following requierements:

* For every object $X$ in $\mathcal{C}$, a morphism $\alpha_{\mathcal{C}} : F(X) \rightarrow G(X)$ between objects of $\mathcal{D}$. The morphism $\alpha_{X}$ is called the component of $\alpha$ at $X$.

* Components must be such tat for every morphism $f : X \rightarrow Y$ in $\mathcal{C}$ we have: $\alpha_{Y} \circ F(f) = G(f) \circ \alpha_{X}$


<!-- A natural tansformation $\phi : F \Rightarrow G$ kk -->
such that the following diagram commute:

{% raw %}
\begin{xy}
\xymatrix{
X \ar[r]_{F\ \ \ } \ar[d]_{f} \ar@/^1.5pc/[rr]^{\alpha_{X}\ \circ\ F} & F(X) \ar[r]_{\alpha_{X}} \ar[d]_{F(f)} & G(X) \ar[d]_{G(f)} \\
Y \ar[r]^{F\ \ \ } \ar@/_1.5pc/[rr]_{\alpha_{Y}\ \circ\ F}  & F(Y) \ar[r]^{\alpha_{Y}}  & G(Y)
}
\end{xy}
{% endraw %}

We denote natural transformations as double arrows, $\alpha : F \Rightarrow G$, to distinguish them in diagrams from usual morphisms:
{% raw %}
\begin{xy}
\xymatrix @=5pc {
\mathcal{C} \rtwocell<5>^{F}_{G}{\alpha} & \mathcal{D}
}
\end{xy}
{% endraw %}

<!-- \mathcal{C} \ar@/^1pc/[rr]^{alpha} && \mathcal{D} -->





Natural transformations are one of the most important aspects of category theory. Saunders Mac Lane, one of the founders of category theory, once said, "I didn't invent categories to study functors; I invented them to study natural transformations."


# Example

The Applicative typeclass in Haskell looks slightly different then our definition of a lax monidal functor. However there is another typeclass in Haskell called Monoidal that reflects our definition. Moreover, there is a equivalence between the two typeclasses Applicative and Monoidal. This parallels our previous demonstration of the interchangeability between `bind` and `>>=`, as discussed in my post on [monads](/monad). Let me first introduce the typeclass Monoidal and then we show that this is equivalent to Applicative.


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

Haskell comes with `curry` and `uncurry` as part of its standard library, which together form an isomorphism. Hence we can also phrase Monoidal in this way, and it aligns seamlessly with our categorical definition of a strong lax monoidal functor:

{% vimhl hs %}
class Functor f => Monoidal f where
-- η     : 1  -> F(1) (unit)
  unit' :: () -> f ()
-- ϕx,y  : F(X) ⊗ F(Y) -> F(X ⊗ Y)
  (**') :: (f a, f b)   -> f (a, b)
{% endvimhl %}


We have the usual monoidal laws (pseudocode):

<!-- -- It's not possible to define laws in Haskell (pseudocode) -->
{% vimhl hs %}
unit ** v == v == v ** unit    -- Left and Right Identity
u ** (v ** w) == (u ** v) ** w -- Associativity
{% endvimhl %}

Now that we have established the definition lets have a look at the equivalent Applicative definition in Haskell.

Haskell Definition of Applicative (Interface)

{% vimhl hs %}
class Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
{% endvimhl %}

This is how to recover Applicative in terms of Monoidal:
{% vimhl hs %}
pure :: Monoidal f => a -> f a
pure x  = fmap (const x) unit

(<*>) :: Monoidal f => f (a -> b) -> f a -> f b
f <*> g = fmap uncurry ($) (f ** g)
{% endvimhl %}

And this is the reverse direction, Monoidal in terms of Applicative:

{% vimhl hs %}
unit :: Applicative f => f ()
unit   = pure ()

(**) :: Applicative f => f a -> f b  -> f (a, b)
f ** g = fmap (,) f <*> g
{% endvimhl %}

We've now formulated a two-way translation between Applicative and Monoidal, illustrating that they are isomorphic. This equality between Applicative and Monoidal has actually be shown in a computer checked [proof](https://stackoverflow.com/a/62959880) in Coq. Now, lets have a look at some instances of Applicative.

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

An Instance of Applicative, the List Applicative
{% vimhl hs %}
instance Functor [] where
 -- pure :: a -> [a]
    pure x    = [x]

 --   (<*>) :: [(a -> b)] -> [a] -> [b]
    fs <*> xs = [f x | f <- fs, x <- xs]
 -- Thats a list comprehension that generates a new list
 -- by applying the function f to each element in the list
 -- xs for every function f in the list fs.
{% endvimhl %}

Another Instance, the Maybe Functor
{% vimhl hs %}
instance Applicative Maybe where
 -- pure :: a -> Maybe a
    pure x                = Just (x)

 -- (<*>) :: Maybe (a -> b) -> Maybe a -> Maybe b
    (Just f) <*> (Just x) = Just (f x)
    _        <*> _        = Nothing
{% endvimhl %}

All of the above is already implemented in the standard Haskell library, so you can also simply open an interactive Haskell interpreter (ghci) and test the following examples.

{% vimhl hs %}
ghci> [(*2)] <*> [1,2,3]
[2,4,6]

ghci> [(+1),(*2)] <*> [1,2,3]
[2,3,4,2,4,6]

ghci> Just (*2) <*> Just (3)
6

ghci> Just (*2) <*> Nothing
Nothing
{% endvimhl %}

### References

[^0]: The diagram displayed at the top of this post is a modified version of Brent Yorgey's [Typeclassopedia diagram](https://wiki.haskell.org/File:Typeclassopedia-diagram.png)
[^1]: McBride, Conor; Paterson, Ross (2008-01-01). *Applicative programming with effects* ([pdf](http://www.staff.city.ac.uk/~ross/papers/Applicative.pdf)). Journal of Functional Programming. 18 (1): 1–13. [doi:10.1017/S0956796807006326](https://doi.org/10.1017/S0956796807006326)
[^2]: Rivas, E., & Jaskelioff, M. (2014). Notions of Computation as Monoids. CoRR, abs/1406.4823. [https://arxiv.org/abs/1406.4823](https://arxiv.org/pdf/1406.4823.pdf)
