---
title: Category
date: 2023-09-14
tags: ["category theory", "haskell"]
subtitle: Collection of Objects Linked by Arrows
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
<img src="/images/category.png" onclick="window.open(this.src)">
<!-- The source as dot is next to image. Compile with: dot -Tsvg typeclasses.dot -o typeclasses.svg -->
<br>

<!-- A category $\mathcal{C}$ is a quadruple $(\text{Obj}(\mathcal{C}), \text{Mor}(\mathcal{C}),\mu,1_\mathcal{C})$ consisting of a collection of objects $\text{Obj}(\mathcal{C})$, -->
<!-- For each pair of objects $A,B$, a set $\text{Hom}(A,B)$ of morphisms, also called [hom-sets](/hom-sets). -->

<!-- composition is associative: for each quadruple $a,b,c,d \in \text{Obj}(\mathcal{C})$ of objects, if $f \in HOM\ Mor?$ -->

A category $\mathcal{C}$ consists of a collection of objects, denoted $\text{Obj}(\mathcal{C})$ and, for every two objects $x, y \in \text{Obj}(\mathcal{C})$, a set of morphisms $\text{Hom}(x,y)$, also called [hom-sets](/hom-sets), satisfying the following properties:

* For every three objects $x,y,z \in \text{Obj}(\mathcal{C})$, there exist a binary operation $\circ$, called composition of morphisms, that satisfies the composition law:

  * $\circ : \text{Hom}(y,z) \times \text{Hom}(x,y) \rightarrow \text{Hom}(x,z)$, that can be written as: $(g,f) \rightarrow g\ \circ\ f$
    <!-- <li style="list-style-type: none;">Item 1</li> -->
    <!-- <li style="list-style-type: none;">Item 2</li> -->

* Composition is associative: for all $w,x,y,z \in \text{Obj}(\mathcal{C}), f \in \text{Hom}(y,z)$, $g \in \text{Hom}(x,y)$, $h \in \text{Hom}(w,x)$ we have:

    * $f \circ (g \circ h) = (f \circ g) \circ h$

* For each $x \in \text{Obj}(\mathcal{C})$, there is a unique element $1_{x} \in \text{Hom}(x,x)$ (identity morphism), such that, for every $y \in \text{Obj}(\mathcal{C})$, we have left and right unit laws:

    * $f \circ 1_{x} = f$ for all $f \in \text{Hom}(x, y)$
    * $1_{x} \circ f = f$ for all $f \in \text{Hom}(y,x)$

<!-- For each $x \in \text{Obj}(\mathcal{C})$, there is a unique element $1_{x} \in \text{Hom}(x,x)$ (identity morphism), such that for every pair $x,y \in \text{Obj}(\mathcal{C})$, if $f \in \text{Hom}(x,y)$, then we have left and right unit laws: -->

<!-- * $1_{y} \circ f = f = f \circ 1_{x}$ -->

It is common to express $x \in \mathcal{C}$ instead of $x \in \text{Obj}(\mathcal{C})$ and when indicating 'f is a function from x to y', it's typically written as $f: x \rightarrow y$ rather than $f \in \text{Hom}(x,y)$. A category is a very general concept, the objects and morphisms can be anything, as long as they adhere to the stated conditions. The following is an example category with a collection of objects $X, Y, Z$ and collection of morphisms denoted $f, g, g \circ f$, and the loops are the identity morphisms.

{% raw %}
\begin{xy}
	\xymatrix{
	X \ar@(l,u)^{1_X}[] \ar_{g\ \circ\ f}[dr] \ar^f[r] & Y \ar@(u,r)^{1_Y}[] \ar^g[d]\\
	&Z \ar@(d,r)_{1_Z}[]
	}
\end{xy}
{% endraw %}



One interesting aspect that follows from the left and right unit laws is that the identity morphism is unique, so there really is just one way to loop back to itself.
<div class="proof" >

**Proposition.** &nbsp; *The identity morphism is unique.*
*Proof.* &nbsp; Suppose that each of $1_{x}$ and $1'_{x}$ is an identity morphism. Then by left and right unit laws we have: $1'_{x} \circ 1_{x} = 1'_{x}$ and $1'_{x} \circ 1_{x} = 1_{x}$, hence $1'_{x} = 1'_{x} \circ 1_{x} = 1_{x}$
<div class="right">

$\pmb{\scriptstyle \square}$
</div> </div>

Here is an alternative formulation of this proof in [Coq](https://gist.github.com/madnight/f1d0f4d2d21b645549365056c4d4ae75).

<!-- Clean proof style -->
<!-- https://math.berkeley.edu/~wodzicki/253.F16/Cat.pdf -->

<!-- https://www.heldermann.de/SSPM/SSPM01/Chapter-3.pdf -->



<!-- Section Category. -->
<!--   Context `{Hom : Type -> Type -> Type}. -->

<!--   Class Category := { -->
<!--     id : forall {X}, Hom X X; -->
<!--     compose  : forall {X Y Z}, Hom X Y -> Hom Y Z -> Hom X Z; -->

<!--     (* Identity Laws *) -->
<!--     left_identity  : forall {X Y} (f: Hom X Y), -->
<!--       compose id f = f; -->
<!--     right_identity : forall {X Y} (f: Hom X Y), -->
<!--       compose f id = f; -->
<!--   }. -->

<!--   Variables X : Type. -->
<!--   Variables (id1 id2 : Hom X X). -->
<!--   Context `{C : @Category Hom}. -->

<!--   Hypothesis H1 : forall {Y} (f : Hom X Y), compose id1 f = f. -->
<!--   Hypothesis H2 : forall {Y} (f : Hom X Y), compose id2 f = f. -->

<!--   Theorem identity_unique : id1 = id2. -->
<!--   Proof. -->
<!--     specialize H1 with (f:=id1). -->
<!--     specialize H2 with (f:=id1). -->
<!--     rewrite <- H1 in H2. -->
<!--     exact H2. -->
<!--   Qed. -->

# Example

In Haskell objects are types and morphisms are functions.

 In Haskell, the identity morphism is id, and we have trivially:
```hs
id . f = f . id = f

f g h = (f . g) . h = f . (g . h)
```

{% vimhl hs %}
class Category cat where
    -- the identity morphism
    id :: cat a a

    -- morphism composition
    (.) :: (b `cat` c) -> (a `cat` b) -> (a `cat` c)
{% endvimhl %}

askell types along with functions between types form (almost†) a category. We have an identity morphism (function) (id :: a -> a) for every object (type) a; and composition of morphisms ((.) :: (b -> c) -> (a -> b) -> a -> c), which obey category laws:

The category laws state that id is the identity for composition and that composition is associative.

In Haskell, we implement the standard category as follows:



{% vimhl hs %}
instance Category (->) where
    id :: a -> a
    id x = x

    (.) :: (b -> c) -> (a -> b) -> a -> c
    g . f = \x -> g (f x)
{% endvimhl %}

This instance represents the category of Haskell types and functions.


In Haskell, the 'Objects of a Category' are defined by types. The typeclass variable `cat` characterizes the variety of morphisms in the given category, particularly when the origins and destinations of our morphisms are concealed in the morphisms' type declarations for which we establish a category instance. In the instance of `(->)`, the origin and destination can be any data type in Haskell. Conversely, for a Kleisli morphism, the source can be any Haskell data type, but the target must conform to the `m a` structure for some `m`. This allows us to sketch the constitution of a morphism in the category, but it doesn't lay out all the laws for free (Consider Grp encoding, for example).


We can convince ourself that this laws actually hold:

{% vimhl hs %}
-- Left identity: id . f = f
id . f
= \x -> id (f x)
= \x -> f x
= f

-- Right identity: f . id = f
f . id
= \x -> f (id x)
= \x -> f x
= f

-- Associativity: (f . g) . h = f . (g . h)
(f . g) . h
= \x -> (f . g) (h x)
= \x -> f (g (h x))
= \x -> f ((g . h) x)
= \x -> (f . (g . h)) x
= f . (g . h)
{% endvimhl %}

Another common example is the Category of Kleisli arrows for a Monad:

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

<!-- We usually call this category Hask. -->

<!-- https://hackage.haskell.org/package/base-4.6.0.1/docs/Control-Arrow.html -->
<!-- is category -->

<!-- The canonical example of a Category in Haskell is the function category: -->

<!-- Another common example is the Category of Kleisli arrows for a Monad: -->

The Category type class in Haskell isn't typically used for everyday programming tasks, but it does have a few interesting and practical applications. Some of these include:


Interesting:
https://devtut.github.io/haskell/applicative-functor.html#alternative-definition

class Functor f => PairingFunctor f where
  funit :: f ()                  -- create a context, carrying nothing of import
  fpair :: (f a,f b) -> f (a,b)  -- collapse a pair of contexts into a pair-carrying context


This class is isomorphic to Applicative.

pure a = const a <$> funit = a <$ funit  
fa <*> fb = (\(a,b) -> a b) <$> fpair (fa, fb) = uncurry ($) <$> fpair (fa, fb)

And inverse:


funit = pure ()

fpair (fa, fb) = (,) <$> fa <*> fb



A correct instance of Applicative should satisfy the applicative laws, though these are not enforced by the compiler:

pure id <*> a = a                              -- identity
pure (.) <*> a <*> b <*> c = a <*> (b <*> c)   -- composition
pure f <*> pure a = pure (f a)                 -- homomorphism
a <*> pure b = pure ($ b) <*> a                -- interchange

Here are some more examples:

* Set, the category of sets and set functions
* Mon, the category of monoids and monoid morphisms
* Monoids are themselves one-object categories
* Grp, the category of groups and group morphisms
* Rng, the category of rings and ring morphisms
* Grph, the category of graphs and graph morphisms
* Top, the category of topological spaces and continuous maps
* Preord, the category of preorders and order preserving maps
* CPO, the category of complete partial orders and continuous functions
* Cat, the category of categories and functors
* The category of data types and functions on data structures
* The category of functions and data flows (data flow diagram)
* The category of stateful objects and dependencies (object diagram)
* The category of values and value constructors
* The category of states and messages (state diagram)

### References

[^0]: The diagram displayed at the top of this post is a modified version of Brent Yorgey's [Typeclassopedia diagram](https://wiki.haskell.org/File:Typeclassopedia-diagram.png)
