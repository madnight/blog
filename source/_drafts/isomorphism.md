---
title: Isomorphism
date: 2023-10-15
tags: ["category theory", "haskell"]
subtitle: A Morphism with Inverse
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


<link rel="stylesheet" type="text/css" href="http://tikzjax.com/v1/fonts.css">
<script src="https://tikzjax-demo.glitch.me/tikzjax.js"></script>

<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3.1.4/es5/tex-chtml-full.js"></script>
<script>
window.addEventListener('load', function() {
   document.querySelectorAll("mjx-xypic-object").forEach( (x) => (x.style.color = "var(--darkreader-text--text"));
   document.querySelectorAll("mjx-math > mjx-xypic > svg > g").forEach(x => x.setAttribute("stroke", "var(--darkreader-text--text"))
})
</script>

{% endraw %}

<!-- <br> -->
<!-- <img src="/images/applicative.png" onclick="window.open(this.src)"> -->
<!-- The source as dot is next to image. Compile with: dot -Tsvg typeclasses.dot -o typeclasses.svg -->
<!-- <br> -->

Let $\mathcal{C}$ be a [category](/category) and $A, B$ be objects of $\mathcal{C}$, an isomorphism is a morphism $f : A \rightarrow B$ if and only if there exists an inverse morphism $g : B \rightarrow A$, such that, $f \circ g = 1_{B}$ and $g \circ f = 1_{A}$, where $1_{A}$ denotes the identity morphism on $A$, in which case one writes $A \cong B$.

{% raw %}
\begin{xy}
\xymatrix{
A \ar@/^1.0pc/[rr]^{f}  && B \ar@/^1.0pc/[ll]^{g}
}
\end{xy}
{% endraw %}

Two categories $\mathcal{C}$ and $\mathcal{D}$ are isomorhphic if there exist [functors](/functor) $F : \mathcal{C} \rightarrow \mathcal{D}$ and $G : D \rightarrow C$ which are mutually inverse to each other, that is, $F \circ G = 1_{D}$ and $G \circ F = 1_{C}$.

{% raw %}
\begin{xy}
\xymatrix{
\mathcal{C} \ar@/^1.0pc/[rr]^{F} && \mathcal{D} \ar@/^1.0pc/[ll]^{G}
}
\end{xy}
{% endraw %}

A natural isomorphism is a natural transformation $\eta : F \Rightarrow G$ such that for all $A \in \mathcal{C} , \eta_{A} : F(A) \Rightarrow G(A)$ is an isomorphism. In this case, the natural isomorphism is often written as $\eta : F \cong G$.

{% raw %}
\begin{xy}
\xymatrix @=5pc {
\mathcal{C} \rtwocell<5>^{F(A)}_{G(A)}{\ \ \ \ \eta_{A}} & \mathcal{D} \ltwocell<5>^{G(A)}_{F(A)}{\ \ \ \ \eta_{A}}
}
\end{xy}
{% endraw %}


<!-- {% raw %} -->
<!-- \begin{xy} -->
<!-- \xymatrix{ -->
<!-- A\ar[d]\ar[r]\xtwocell[0,1]{}\omit{<2>} & B\\ -->
<!-- C\ar@{.>}[ur] & -->
<!-- } -->
<!-- \end{xy} -->
<!-- {% endraw %} -->

A
<!-- {% raw %} -->
<script type="text/tikz">
  \begin{tikzpicture}
    \draw (0,0) circle (1in);
  \end{tikzpicture}
</script>
<!-- {% endraw %} -->
B
<!-- {% raw %} -->
<!-- \begin{xy} -->
<!-- \xymatrix @=5pc { -->
<!-- P \rtwocell~!~’{\dir{>>}}~‘{\dir{|}} ^{<1.5>M}_{<1.5>M’}{=f} & S -->
<!-- } -->
<!-- \end{xy} -->
<!-- {% endraw %} -->




<div class="proof" >

**Proposition.** &nbsp; *Identity morphism are isomorphisms.*

*Proof.* &nbsp; To show that $1_A$ is an isomorphism, we need to find an inverse morphism $g$ such that $g \circ 1_{A} = 1_{A} \circ g = 1_{A}$. Let's take $g$ to be $1_{A}$ itself. Then we have $1_{A} \circ 1_{A} = 1_{A}$ since the composition of the identity arrow with itself is the identity arrow by definition. Hence, $1_{A}$ is an isomorphism with inverse $1_{A}$.
<!-- $\pmb{\scriptstyle \square}$ -->
<div class="right">

$\pmb{\scriptstyle \square}$
</div> </div>

<details>
  <summary>In Coq.</summary>
  <div class="coq">
{% vimhl hs %}
Section IdentityIsomorphism.
  Variable Obj : Type.
  Variable Hom : Obj -> Obj -> Type.

  Variable id : forall A : Obj, Hom A A.
  Variable composition : forall {X Y Z : Obj},
    Hom Y Z -> Hom X Y -> Hom X Z.

  Notation "g 'o' f" := (composition g f) (at level 50).

  Hypothesis id_left : forall A B : Obj,
    forall f : Hom A B, (id B) o f = f.
  Hypothesis id_right : forall A B : Obj,
    forall f : Hom A B, f o (id A) = f.

  Proposition identity_is_isomorphism :
    forall A : Obj, (id A) o (id A) = id A.
  Proof.
    intros A.
    rewrite <- id_right.
    reflexivity.
  Qed.
End IdentityIsomorphism.
{% endvimhl %}
  </div>
</details>

<!-- Here is an alternative formulation of this proof in [Coq](https://gist.github.com/madnight/4d00970f1944a66113d7f04465af20f8). -->

The term isomorphism originates from the Greek word morphe (μορφή), which translates to form or structure, and the prefix iso-, signifying equal. Consequently, isomorphism implies having an equal structure.

<!-- https://www.logicmatters.net/resources/pdfs/SmithCat-I.pdf 76 -->
<!-- https://arxiv.org/pdf/1912.10642.pdf 16 -->
<!-- https://math.jhu.edu/~eriehl/context.pdf 42 -->
<!-- https://proofwiki.org/wiki/Definition:Natural_Isomorphism -->

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
-- Proposition.
fmap f . safeHead = safeHead . fmap f

-- Case Nothing.
fmap f (safeHead []) = fmap f Nothing = Nothing
safeHead (fmap f []) = safeHead [] = Nothing

-- Case non-empty List.
fmap f (safeHead (x:xs)) = fmap f (Just x) = Just (f x)
safeHead (fmap f (x:xs)) = safeHead (f x : fmap f xs) = Just (f x)

-- Qed.
{% endvimhl %}

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

Bou can open an interactive Haskell interpreter (ghci), load the functions and test the following examples.

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
