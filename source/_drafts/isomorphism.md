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


<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3.1.4/es5/tex-chtml-full.js"></script>

<script id="dark-toggle" async src="/js/dark-toggle.js"></script>

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

<!-- A natural isomorphism is a natural transformation $\eta : F \Rightarrow G$ such that for all $A \in \mathcal{C} , \eta_{A} : F(A) \Rightarrow G(A)$ is an isomorphism. In this case, the natural isomorphism is often written as $\eta : F \cong G$. -->

A natural isomorphism is a [natural transformation](/natural-transformation) $\eta : F \Rightarrow G$ if there exist an inverse natural transformation $\mu : G \Rightarrow F$, such that the compositions $\mu \circ \eta = 1_{F}$ and $\eta \circ \mu = 1_{G}$ are identity natural transformations.

{% raw %}
\begin{xy}
\xymatrix {
F \ar@/^1.0pc/[rr]^{\eta} && G \ar@/^1.0pc/[ll]^{\mu}
}
\end{xy}
{% endraw %}


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

In Haskell, we can define an isomorphism like so:

{% vimhl hs %}
data Isomorphism a b = Isomorphism
    { forward  :: a -> b
    , backward :: b -> a
    }
{% endvimhl %}

We say that two types a and b are isomorphic in Haskell if there is a pair of functions `f :: a -> b` and `g :: b -> a` satisfying `f . g = id` and `g . f = id`.

One typical example for an isomorphism in Haskell is curry and uncurry.

{% vimhl hs %}
curry :: ((a, b) -> c) -> a -> b -> c
curry f x y = f (x, y)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f p = f (fst p) (snd p)

currying :: Isomorphism ((a, b) -> c) (a -> b -> c)
currying = Isomorphism { forward = curry, backward = uncurry }
{% endvimhl %}

Haskell comes with `curry` and `uncurry` as part of its standard library, which together form an isomorphism.


{% raw %}
\begin{xy}
\xymatrix@C-=1cm{
\texttt{(a, b) -> c} \ar@/^1.5pc/[rr]^{\texttt{curry}}  && \texttt{a -> b -> c} \ar@/^1.5pc/[ll]^{\texttt{uncurry}}}
\end{xy}
{% endraw %}

The `swap` isomorphism is another example and a special case of an isomorphism in Haskell. It is a function that swaps the order of a tuple's elements. For example, the swap function for a tuple of two elements (a, b) would return (b, a). This function is special because it is its own inverse, meaning that applying the swap function twice returns the original tuple. 

{% vimhl hs %}
swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

isoswap :: Isomorphism (a, b) (b, a)
isoswap = Isomorphism { forward = swap, backward = swap }
{% endvimhl %}


{% raw %}
\begin{xy}
\xymatrix@C-=1cm{
\texttt{(a, b)} \ar@/^1.5pc/[rr]^{\texttt{swap}}  && \texttt{(b, a)} \ar@/^1.5pc/[ll]^{\texttt{swap}}}
\end{xy}
{% endraw %}

Bou can open an interactive Haskell interpreter (ghci), load the functions and test the following examples.

{% vimhl hs %}
ghci> forward isoswap (1,2)
(2,1)

ghci> backward isoswap $ forward isoswap (1,2)
(1,2)

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
