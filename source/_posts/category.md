---
title: Category
date: 2023-10-02
tags: ["category theory", "haskell"]
subtitle: Collection of Objects Linked by Arrows
categories:
  - Computer Science
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

<style>
<!-- li { -->
  <!-- list-style-type: none; -->
<!-- } -->
ul > li {
  list-style-type: disc;
}
.code-box {
    position: relative;
    padding-top: 12px;
    margin-top: -0.5rem;
}
.language-label {
    position: absolute;
    top: 0;
    left: 0;
    background-color: #20211f;
    padding: 2px 5px;
    border-color: rgb(59, 60, 58);
    border-top: 1px solid #393a38;
    border-right: 1px solid #393a38;
    border-left: 1px solid #393a38;
    font-size: 0.9rem;
    text-align: right; /* Aligns the text to the right */
}
</style>
{% endraw %}

<br>
<div class=typeclass>
<img src="/images/category.svg" onclick="window.open(this.src)">
</div>
<!-- The source as dot is next to image. Compile with: dot -Tsvg typeclasses.dot -o typeclasses.svg -->
<br>

<!-- A category $\mathcal{C}$ is a quadruple $(\text{Obj}(\mathcal{C}), \text{Mor}(\mathcal{C}),\mu,1_\mathcal{C})$ consisting of a collection of objects $\text{Obj}(\mathcal{C})$, -->
<!-- For each pair of objects $A,B$, a set $\text{Hom}(A,B)$ of morphisms, also called [hom-sets](/hom-sets). -->

<!-- composition is associative: for each quadruple $a,b,c,d \in \text{Obj}(\mathcal{C})$ of objects, if $f \in HOM\ Mor?$ -->

A category $\mathcal{C}$ consists of a collection of objects, denoted $\text{Obj}(\mathcal{C})$ and, for every two objects $A, B \in \text{Obj}(\mathcal{C})$, a set of morphisms $\text{Hom}(A,B)$, also called [hom-sets](/hom-set), satisfying the following properties:

* For every three objects $A,B,C \in \text{Obj}(\mathcal{C})$, there exist a binary operation $\circ$, called composition of morphisms, that satisfies the composition law:

  * $\circ : \text{Hom}(B,C) \times \text{Hom}(A,B) \rightarrow \text{Hom}(A,C)$, that can be written as: $(g,f) \rightarrow g\ \circ\ f$
    <!-- <li style="list-style-type: none;">Item 1</li> -->
    <!-- <li style="list-style-type: none;">Item 2</li> -->

* Composition is associative: for all $A,B,C,D \in \text{Obj}(\mathcal{C}), f \in \text{Hom}(B,C)$, $g \in \text{Hom}(A,B)$, $h \in \text{Hom}(D,A)$ we have:

    * $f \circ (g \circ h) = (f \circ g) \circ h$

* For each $A \in \text{Obj}(\mathcal{C})$, there is a unique element $1_{A} \in \text{Hom}(A,A)$ (identity morphism), such that, for every $B \in \text{Obj}(\mathcal{C})$, we have left and right unit laws:

    * $f \circ 1_{A} = f$ for all $f \in \text{Hom}(A, B)$
    * $1_{A} \circ f = f$ for all $f \in \text{Hom}(B,A)$

<!-- For each $x \in \text{Obj}(\mathcal{C})$, there is a unique element $1_{x} \in \text{Hom}(x,x)$ (identity morphism), such that for every pair $x,y \in \text{Obj}(\mathcal{C})$, if $f \in \text{Hom}(x,y)$, then we have left and right unit laws: -->

<!-- * $1_{y} \circ f = f = f \circ 1_{x}$ -->

It is common to express $A \in \mathcal{C}$ instead of $A \in \text{Obj}(\mathcal{C})$ and when indicating $f$ is a function from $A$ to $B$, it's typically written as $f: A \rightarrow B$ rather than $f \in \text{Hom}(A,B)$.

A category is a very general concept, the objects and morphisms can be anything, as long as they adhere to the stated conditions. The following is an example category with a collection of objects $A, B, C$ and collection of morphisms denoted $f, g, g \circ f$, and the loops are the identity morphisms.

{% raw %}
\begin{xy}
	\xymatrix{
	A \ar@(l,u)^{1_A}[] \ar_{g\ \circ\ f}[dr] \ar^f[r] & B \ar@(u,r)^{1_B}[] \ar^g[d]\\
	&C \ar@(d,r)_{1_C}[]
	}
\end{xy}
{% endraw %}



One interesting aspect that follows from the left and right unit laws is that the identity morphism is unique, so there really is just one way to loop back to itself.
<div class="proof" >

**Proposition.** &nbsp; *The identity morphism is unique.*

*Proof.* &nbsp; Suppose that each of $1_{A}$ and $1'_{A}$ is an identity morphism. Then by left and right unit laws we have: $1'_{A} \circ 1_{A} = 1'_{A}$ and $1'_{A} \circ 1_{A} = 1_{A}$, hence $1'_{A} = 1'_{A} \circ 1_{A} = 1_{A}$
<div class="right">

$\pmb{\scriptstyle \square}$
</div> </div>

<details>
  <summary>In Coq.</summary>
  <div class="coq">
{% vimhl hs %}
Section Category.
  Variable Obj : Type.
  Variable Hom : Obj -> Obj -> Type.

  Variable composition : forall {X Y Z : Obj},
      Hom Y Z -> Hom X Y -> Hom X Z.
  Notation "g 'o' f" := (composition g f) (at level 50).

  Variable id : forall {X : Obj}, Hom X X.

  Hypothesis id_left : forall {X Y : Obj} (f : Hom X Y), id o f = f.
  Hypothesis id_right : forall {X Y : Obj} (f : Hom X Y), f o id = f.

  Theorem id_unique : forall {X : Obj} (id1 id2 : Hom X X),
        (forall {Y : Obj} (f : Hom Y X), id1 o f = f) ->
        (forall {Y : Obj} (f : Hom X Y), f o id1 = f) ->
        (forall {Y : Obj} (f : Hom Y X), id2 o f = f) ->
        (forall {Y : Obj} (f : Hom X Y), f o id2 = f) ->
        id1 = id2.
    Proof.
      intros X id1 id2 H1 H2 H3 H4.
      transitivity (id o id1).
      - symmetry.
        apply id_left.
      - transitivity (id o id2).
        + rewrite H2.
          symmetry.
          rewrite H4.
          reflexivity.
        + apply id_left.
    Qed.
End Category.
{% endvimhl %}
  </div>
</details>

<!-- Clean proof style -->
<!-- https://math.berkeley.edu/~wodzicki/253.F16/Cat.pdf -->

<!-- https://www.heldermann.de/SSPM/SSPM01/Chapter-3.pdf -->



<!-- Section Category. -->
<!--   Context `{Hom : Type -> Type -> Type}. -->

<!--   Class Category := { -->
<!--     id : forall {A}, Hom A A; -->
<!--     compose  : forall {A B C}, Hom A B -> Hom B C -> Hom A C; -->

<!--     (* Identity Laws *) -->
<!--     left_identity  : forall {A B} (f: Hom A B), -->
<!--       compose id f = f; -->
<!--     right_identity : forall {A B} (f: Hom A B), -->
<!--       compose f id = f; -->
<!--   }. -->

<!--   Variables A : Type. -->
<!--   Variables (id1 id2 : Hom A A). -->
<!--   Context `{C : @Category Hom}. -->

<!--   Hypothesis H1 : forall {B} (f : Hom A B), compose id1 f = f. -->
<!--   Hypothesis H2 : forall {B} (f : Hom A B), compose id2 f = f. -->

<!--   Theorem identity_unique : id1 = id2. -->
<!--   Proof. -->
<!--     specialize H1 with (f:=id1). -->
<!--     specialize H2 with (f:=id1). -->
<!--     rewrite <- H1 in H2. -->
<!--     exact H2. -->
<!--   Qed. -->

# Example

In Haskell, Category is a type class that abstracts the concept of a mathematical category. In the context of Haskell, types are considered as objects and functions as morphisms.

{% vimhl hs %}
class Category cat where
    -- the identity morphism
    --    Hom(A, A)
    id :: a `cat` a

    -- morphism composition
    --      Hom(B, C)   ×   Hom(A, B)  →  Hom(A, C)
    (.) :: (b `cat` c) -> (a `cat` b) -> (a `cat` c)
{% endvimhl %}


In Haskell, one traditionally works in the category (->) called **Hask**, in which any Haskell type is an object and functions are morphisms. We can implement **Hask** as follows:

{% vimhl hs %}
instance Category (->) where
    id :: a -> a
    id x = x

    (.) :: (b -> c) -> (a -> b) -> a -> c
    g . f = \x -> g (f x)
{% endvimhl %}

As we can see, `cat` has simply been replaced by Haskell arrows. The `id` function is the identity morphism that leaves the object unchanged. The `(.)` function is a composition of morphisms, which obey category laws in pseudo notation:

{% vimhl hs %}
id . f = f . id = f       -- left and right identity law
(f . g) . h = f . (g . h) -- composition is associative
{% endvimhl %}

Haskell faces some challenges when considered in its entirety as category **Hask** due to features like non-termination and bottom values. Therefore, when speaking about **Hask** it is often referred to a constrained subset of Haskell that excludes these problematic aspects. Specifically, this subset only permits terminating functions operating on finite values. It also resolves other subtleties. In essence, this pragmatic subset removes everything preventing Haskell from being modeled as a category.

<!-- The corresponding category has the expected initial and terminal objects, sums and products, and instances of Functor and Monad really are endofunctors and monads 1. -->

The Category typeclass[^1] can also be used with other structures that can be viewed as categories, not just functions between types. For example, it can be used with the Kleisli category of a [monad](/monad), where morphisms are functions of type `a -> m b`. The objects in this category are identical to the types in Haskell as found in `Hask`. However, the transformation between these entities are represented by Kleisli arrows. 


<!-- Within the context of Kleisli, the composition operation becomes the Kleisli composition operator (<=<), and the identity transformation, possessing type `a -> m a`, is denoted as `return`. -->


{% vimhl hs %}
newtype Kleisli m a b = Kleisli {
    runKleisli :: a -> m b
}

instance Monad m => Category (Kleisli m) where
    id :: Kleisli m a a
    id = Kleisli return

    (.) :: Kleisli m b c -> Kleisli m a b -> Kleisli m a c
    Kleisli f . Kleisli g = Kleisli (join . fmap g . f)
{% endvimhl %}

Kleisli arrows are a way of composing monadic programs. They are a notational feature that can be useful, but they don't provide any additional functionality beyond what the monad already provides. The use of this syntax in Haskell, since it overwrites `id` and standard function composition `(.)`, can be quite confusing if used in this manner. Instead, Kleisli composition is often defined using the "fish" operator, as shown below:

{% vimhl hs %}
(<=<) :: Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
(g <=< f) a = f a >>= g

-- m >>= f = (f <=< return) m
{% endvimhl %}

As we can see <=< can be expressed in terms of `>>=` and vice versa, hence they form an isomorphism. All of the above is already implemented in the standard Haskell library, so you can simply open an interactive Haskell interpreter (ghci) and test the following examples:

{% vimhl hs %}
ghci> (show . (*2) . sqrt . (+2) . abs) 14
"8.0"

ghci> import Control.Monad
ghci> (Just . (+2)) <=< (Just 2 >>=) $ return
Just 4

ghci> putStrLn <=< (getLine >>=) $ return
Hello World
Hello World

{% endvimhl %}

Here are some more examples:

* $\mathbf{Set}$, the category of sets and set functions
* $\mathbf{Mon}$, the category of monoids and monoid morphisms
* $\mathbf{Grp}$, the category of groups and group morphisms
* $\mathbf{Rng}$, the category of rings and ring morphisms
* $\mathbf{Grph}$, the category of graphs and graph morphisms
* $\mathbf{Top}$, the category of topological spaces and continuous maps
* $\mathbf{Preord}$, the category of preorders and order preserving maps
* $\mathbf{CPO}$, the category of complete partial orders and continuous functions
* $\mathbf{Cat}$, the category of categories and functors
* Monoids are themselves one-object categories
* The category of data types and functions on data structures
* The category of functions and data flows (data flow diagram)
* The category of stateful objects and dependencies (object diagram)
* The category of values and value constructors
* The category of states and messages (state diagram)

### References

[^0]: The diagram displayed at the top of this post is a modified version of Brent Yorgey's [Typeclassopedia diagram](https://wiki.haskell.org/File:Typeclassopedia-diagram.png)
[^1]: [Control.Category](https://hackage.haskell.org/package/base-4.18.1.0/docs/Control-Category.html)



