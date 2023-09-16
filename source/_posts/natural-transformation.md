---
title: Natural Transformation
date: 2023-09-12
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

<!-- <br> -->
<!-- <img src="/images/applicative.png" onclick="window.open(this.src)"> -->
<!-- The source as dot is next to image. Compile with: dot -Tsvg typeclasses.dot -o typeclasses.svg -->
<!-- <br> -->

Let $\mathcal{C}$ and $\mathcal{D}$ be categories and $F$ and $G$ be Functors $\mathcal{C} \rightarrow \mathcal{D}$. Then a natural transformation $\alpha$ from $F$ to $G$ is a family of morphism that satisfies the following requirements:

* For every object $X$ in $\mathcal{C}$, a natural transformation $\alpha$ from the functor $F$ to the functor $G$ assigns a morphism $\alpha_{X} : F(X) \rightarrow G(X)$ between objects of $\mathcal{D}$. The morphism $\alpha_{X}$ is called the component of $\alpha$ at $X$.

* Components must be such that for every morphism $f : X \rightarrow Y$ in $\mathcal{C}$ we have: $\alpha_{Y} \circ F(f) = G(f) \circ \alpha_{X}$ (naturality condition)

These requirements can be expressed by the following commutative diagram:

{% raw %}
\begin{xy}
\xymatrix{
X \ar[r]_{F\ \ \ } \ar[d]_{f} \ar@/^1.5pc/[rr]^{\alpha_{X}\ \circ\ F} & F(X) \ar[r]_{\alpha_{X}} \ar[d]_{F(f)} & G(X) \ar[d]_{G(f)} \\
Y \ar[r]^{F\ \ \ } \ar@/_1.5pc/[rr]_{\alpha_{Y}\ \circ\ F}  & F(Y) \ar[r]^{\alpha_{Y}}  & G(Y)
}
\end{xy}
{% endraw %}

We often denote natural transformations as double arrows, $\alpha : F \Rightarrow G$, to distinguish them in diagrams from usual morphisms:
{% raw %}
\begin{xy}
\xymatrix @=5pc {
\mathcal{C} \rtwocell<5>^{F}_{G}{\alpha} & \mathcal{D}
}
\end{xy}
{% endraw %}

<!-- \mathcal{C} \ar@/^1pc/[rr]^{alpha} && \mathcal{D} -->



In other words, a natural transformation is a way of transforming one functor into another while respecting the internal structure of the categories involved. Natural transformations are one of the most important aspects of category theory. Saunders Mac Lane, one of the founders of category theory, once said, "I didn't invent categories to study functors; I invented them to study natural transformations."[^1]


# Example

In Haskell, we can define a natural transformation like so:

{% vimhl hs %}
class (Functor f, Functor g) => Transformation f g where
    alpha :: f a -> g a
{% endvimhl %}

Or we could also define it the following way, as an infix operator (~>):

{% vimhl hs %}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes    #-}

type f ~> g = forall a . f a -> g a
{% endvimhl %}

Again, the requirement of compatibility with the actions of the functors is not expressible as a type signature, but we can write it down as law in pseudocode:

{% vimhl hs %}
alpha (fmap f a) = fmap f (alpha a) -- (naturality condition)
{% endvimhl %}

<!-- The `forall a` is optional in Haskell  -->
<!-- In Haskell, we usually omit the forall quantifier when there’s no danger of confusion. Any signature that contains a type variable is automatically universally quantified over it. -->
Now Haskell supports parametric polymorphism, that means that a function will act on all types uniformly and thus automatically satisfies the naturality condition for any polymorphic function of the type:

{% vimhl hs %}
alpha :: F a -> G a
{% endvimhl %}

where F and G are functors. The naturality condition in terms of Haskell means that it doesn’t matter whether we first apply a function, through the application of `fmap`, and then change the structure via a structure preserving mapping; or first change the structure, and then apply the function to the new structure, with its own implementation of `fmap`. [^2]

Lets have a look at the following example:

{% vimhl hs %}
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:xs) = Just x
{% endvimhl %}

This function returns Nothing in case of an empty list and the first element of the list in case of an non-empty List. This function is called `safeHead`, because there is also a "unsafeHead" in the Haskell standard library, simply called `head`. The unsafe variant throws an Exception in case the List is empty. We can prove by equational reasoning (or [Coq](https://gist.github.com/madnight/903335b1ba1a56b0ae05b2e8df839c38) if you like) that the naturality condition holds in case of `safeHead`:


{% vimhl hs %}
-- Proposition
fmap f . safeHead = safeHead . fmap f

-- Case Nothing
fmap f (safeHead []) = fmap f Nothing = Nothing
safeHead (fmap f []) = safeHead [] = Nothing

-- Case non-empty List
fmap f (safeHead (x:xs)) = fmap f (Just x) = Just (f x)
safeHead (fmap f (x:xs)) = safeHead (f x : fmap f xs) = Just (f x)
{% endvimhl %}
<div align="right">

$\square$
</div>

<!-- Require Import List. -->
<!-- Import ListNotations. -->
<!-- Require Import FunInd. -->
<!-- Require Import Coq.Init.Datatypes. -->

<!-- Inductive Maybe (A:Type) : Type := -->
<!--   | Just : A -> Maybe A -->
<!--   | Nothing : Maybe A. -->

<!-- Arguments Just {A} a. -->
<!-- Arguments Nothing {A}. -->

<!-- Class Functor (F : Type -> Type) := { -->
<!--   fmap : forall {A B : Type}, (A -> B) -> F A -> F B -->
<!-- }. -->

<!-- #[local] -->
<!-- Instance Maybe_Functor : Functor Maybe := -->
<!-- { -->
<!--   fmap A B f x := match x with -->
<!--                    | Nothing => Nothing -->
<!--                    | Just y => Just (f y) -->
<!--                    end -->
<!-- }. -->

<!-- Fixpoint fmap_list {A B : Type} (f: A -> B) (xs: list A) : list B := -->
<!--   match xs with -->
<!--   | nil => nil -->
<!--   | cons y ys => cons (f y) (fmap_list f ys) -->
<!--   end. -->

<!-- #[local] -->
<!-- Instance List_Functor : Functor list := { -->
<!--   fmap A B f l := fmap_list f l -->
<!-- }. -->

<!-- Definition safeHead {A : Type} (l : list A): Maybe A := -->
<!--   match l with -->
<!--   | [] => Nothing -->
<!--   | x :: _ => Just x -->
<!--   end. -->

<!-- Functional Scheme safeHead_ind := Induction for safeHead Sort Prop. -->

<!-- Lemma safeHead_is_natural : -->
<!--   forall (A B : Type) (f : A -> B) (l : list A), -->
<!--      fmap f (safeHead l) = safeHead (fmap f l). -->
<!-- Proof. -->
<!--   intros A B f l. -->
<!--   functional induction (safeHead l); simpl. -->
<!--   - (* Case: l = [] *) -->
<!--     (* The safeHead of an empty list is Nothing, and mapping any function over *) -->
<!--     (* Nothing gives Nothing. On the other hand, mapping any function over an *) -->
<!--     (* empty list gives an empty list and applying safeHead to an empty list *) -->
<!--     (* gives Nothing. Hence in this case, both sides of the equation are Nothing *) -->
<!--     (* which makes them equal. *) -->
<!--     reflexivity. -->
<!--   - (* Case: l = x :: ls for some x and ls *) -->
<!--     (* The safeHead of a list beginning with x is Just x, and mapping f over *) -->
<!--     (* Just x gives Just (f x). On the other hand, mapping f over a list *) -->
<!--     (* beginning with x gives a list beginning with f x and applying safeHead *) -->
<!--     (* to this new list gives Just (f x). Hence in this case, both sides of *) -->
<!--     (* the equation are Just (f x) which makes them equal. *) -->
<!--     reflexivity. -->
<!-- Qed. -->

Here are some more natural transformations:

{% vimhl hs %}
eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe (Left _)  = Nothing
eitherToMaybe (Right x) = Just x

identityToMaybe :: Identity a -> Maybe a
identityToMaybe (Identity x) = Just x

maybeToList  :: Maybe a -> [a]
maybeToList  Nothing   = []
maybeToList  (Just x)  = [x]

maybeToList2 :: Maybe a -> [a]
maybeToList2 Nothing = []
maybeToList2 (Just x) = [x,x]

maybeToList3 :: Maybe a -> [a]
maybeToList3 Nothing = []
maybeToList3 (Just x) = [x,x,x]

-- ...
{% endvimhl %}

As we can see there is an infinite number of natural transformations.

You can open an interactive Haskell interpreter (ghci), load the functions and test the following examples.

{% vimhl hs %}
ghci> safeHead [1,2,3]
Just 1

ghci> safeHead []
Nothing

ghci> maybeToList2 Nothing
[]

ghci> maybeToList3 (Just "Hi")
["Hi","Hi","Hi"]
{% endvimhl %}

### References

[^1]: Mac Lane, Saunders (1998), Categories for the Working Mathematician, Graduate Texts in Mathematics 5 (2nd ed.), Springer-Verlag, p. 16, ISBN 0-387-98403-8
[^2]: [Natural Transformations by Bartosz Milewski (2015)](https://bartoszmilewski.com/2015/04/07/natural-transformations/)
