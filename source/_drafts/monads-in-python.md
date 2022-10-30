---
title: Monads in Python
date: 2022-10-29
tags: ["python", "haskell", "monads", "functional programming"]
subtitle: Functor, Applicative, Monads in Python
---


# Functor

This is how a Functor in Haskell looks like. Althougt it is named class in Haskell you can think of it as an interface. This interface states that in order for something to be a Functur it has to implement the fmap (or map) function. A Functor is also called "mappable", because it is something we can map over like a List.

{% vimhl hs %}
class Functor f where
  fmap :: fa -> (a -> b) -> f b
{% endvimhl %}

In Python we can use type hints to implement the Functor interface for List.


{% vimhl py %}
class FunctorList(List[a]):

  def fmap(fa, f: (a, b)) -> f[b]:
      return FunctorList([f(x) for x in fa])

print(
  FunctorList([1, 2, 3])
    .fmap(lambda x: x + 1)
    .fmap(lambda x: str(x))
    .fmap(lambda x: x + "0")
)

# Result: ['20', '30', '40']
{% endvimhl %}

As you can see the imlemtation of the List Functor is very straight forward. The fmap function simply takes a list fa and applies the function given in the second argument of fmap to every element of the list. As you can see we are now able to apply lambda functions to every list element and chain the results by repeated fmap calls. There is also a builtin function in python for `[f(x) for x in fa]` simply called `map`. The same code in Haskell would look like: `(++"0") <$> (show) <$> (+ 1) <$> [1,2,3]`.

# Applicative

Next thing we are going to impelemt is Applicative. The Interface for Applicative looks as follows:
{% vimhl hs %}
class Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
{% endvimhl %}

We have to implement two functions. The first one is very simple. Given a type `a` lets say Integer, we simply have to put it into our structure, e.g. Int -> [Int]. And the second function states, that given two Applicatives, e.g. two Lists, and one containing a List with a function, we simply apply the functions of that List to every element of the other List.


{% vimhl py %}
class ApplicativeList(FunctorList):

    def pure(a) -> m[a]:
        return ApplicativeList(a)

    def apply(fs, xs) -> f[b]:
      return ApplicativeList([f(x) for f in xs for x in fs])

print(
  ApplicativeList([1, 2, 3])
    .apply([(lambda x: x + 1)])
    .apply([(lambda x: str(x))])
    .apply([(lambda x: x + "0")])
)

# Result: ['20', '30', '40']
{% endvimhl %}

This is very similar to the implementation of Applicative for Lists in Haskell `fs <*> xs = [f x | f <- fs, x <- xs]` and `[(++"0")] <*> ([(show)] <*> ([(+ 1)] <*> [1,2,3]))` yields the same result.

# Monad

{% vimhl hs %}
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

instance Monad [] where
  return :: a -> m a
  return x = [x]

  (>>=) :: m a -> (a -> m b) -> m b
  xs >>= f = concat (map f xs)
{% endvimhl %}


{% vimhl ts %}
class MyClass {
  public static myValue: string;
  constructor(init: string) {
    this.myValue = init;
  }
}
import fs = require("fs");
module MyModule {
  export interface MyInterface extends Other {
    myProperty: any;
  }
}
declare magicNumber number;
myArray.forEach(() => { }); // fat arrow syntax
{% endvimhl %}

{% vimhl py %}
class MonadList(ApplicativeList):

    def pure(a) -> m[a]:
        return MonadList(a)

    def __rshift__(xs, f: (a, m[b])) -> m[b]:
        return MonadList(concat (map(f, xs)))

print(
  "MonadList\n",
  MonadList([1, 2, 3])
    >> (lambda x: [x + 1])
    >> (lambda x: [str(x)])
    >> (lambda x: [x + "0"])
{% endvimhl %}




{% vimhl py %}


"""A List Monad."""
from __future__ import annotations
from itertools import chain

from typing import Any as b
from typing import Callable as Function
from typing import Iterable as Functor
from typing import List
from typing import TypeVar

a = TypeVar("T")
concat = chain.from_iterable

class FunctorList(List[a]):

#  fmap :: fa -> (a -> b) -> f b
  def fmap(fa, f: (a, b)) -> f[b]:
      return FunctorList(map(f, fa))

class ApplicativeList(FunctorList):

    def apply(fs, xs) -> f[b]:
#                fs <*> xs = [f x | f <- fs, x <- xs]
      return ApplicativeList([f(x) for f in xs for x in fs])

class MonadList(ApplicativeList):

#  return :: a  -> m a
    def pure(a) -> m[a]:
        return MonadList(a)

#        (>>=) :: m a -> (a -> m b) -> m b
    def __rshift__(xs, f: (a, m[b])) -> m[b]:
#             xs >>= f = concat (map f xs)
        return MonadList(concat (map(f, xs)))



# (++"0") <$> (show) <$> (+ 1) <$> [1,2,3]
print(
  "FunctorList\n",
  FunctorList([1, 2, 3])
    .fmap(lambda x: x + 1)
    .fmap(lambda x: str(x))
    .fmap(lambda x: x + "0")
)



# [(++"0")] <*> ([(show)] <*> ([(+ 1)] <*> [1,2,3]))
print(
  "ApplicativeList\n",
  ApplicativeList([1, 2, 3])
    .apply([(lambda x: x + 1)])
    .apply([(lambda x: str(x))])
    .apply([(lambda x: x + "0")])
)


 #  [1,2,3] >>= \x -> [(x+1)] >>= \x -> [(show x)] >>= \x -> [x ++ "0"]
print(
  "MonadList\n",
  MonadList([1, 2, 3])
    >> (lambda x: [x + 1])
    >> (lambda x: [str(x)])
    >> (lambda x: [x + "0"])
)



#  class Applicative f where
    #  pure :: a -> f a
    #  (<*>) :: f (a -> b) -> f a -> f b


#  class Monad m where
    #  return :: a -> m a
    #  (>>=) :: m a -> (a -> m b) -> m b


#  instance Monad [] where
    #  return :: a -> m a
    #  return x = [x]

    #  (>>=) :: m a -> (a -> m b) -> m b
    #  xs >>= f = concat (map f xs)

{% endvimhl %}

## References
[^1]: [Purity of runST is finally proven](https://www.reddit.com/r/haskell/comments/679jd3/purity_of_runst_is_finally_proven)
