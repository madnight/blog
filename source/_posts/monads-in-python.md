---
title: Monads in Python
date: 2022-10-30
tags: ["python", "haskell", "monads", "functional programming"]
subtitle: Functor, Applicative, Monads in Python
---

# Motivation

If you're a programmer you are likely already using Monads quiet frequently. One popular example is Future in Java or Promise in JavaScript. You probably have seen or written code like `fetch(url).then(do this).then(do that)` or you've used the `async/await` syntax. You might have noticed that you cannot get a value out of the Promise. As soon as you write `await` your function has to be `async` (has to be a Promise itself). Or when you use `.then()` you cannot get the value out of the `then`. This is because the value only exist after your Promise (the computation) has be resolved, e.g. an API call has been made and the result has arrived.

In other languages like Haskell also things like Input/Output e.g. printing to the terminal or reading from a file happens to be inside a Monad, similar to the Promise in JavaScript. Because similar to JavaScript where you have to write the keyword `async` to your function definition in order to use `await`, in Haskell you have to specify the Monad type in the type annotation. For instance `String -> IO String` is a function that takes a name for an environment variable e.g. `$HOME` and gives you the contents of that variable.[^1] This operation happens to be of type `IO String` and not just `String` because the contents the environment variable is dependent on your system and can change over time. But pure functions by definition always provide the same output for the same input. Therefore you get back an `IO String` which basically means that as soon as the containing IO operation has been executed you will get back the contents of the  environment variable. This is actually pure, because you always get back the same IO computation given the same input.[^2] Now, if you have a function like `String -> String` then you can be sure that there will be no side effects and no IO computation involved. And most of your functions can look like that, which allows you very easy reasoning of what kind of things can happen in your program, just by reading the type definition.

In this post I want to show you how easy it is to write your own Monad instance in Phyton. I have chosen to implement a list Monad, because it provides easy intuition and has much similarities with the Haskell implementation.  We start by writing a Functor and Applicative instance for list in Python.

# Functor

This is how Functor is defined in Haskell. Although it is named class you can think of it as an interface. This interface states that in order for something to be a Functor it has to implement the `fmap` (or `map`) function. A Functor is also often called "mappable", because it is something we can map over like a list.

{% vimhl hs %}
class Functor f where
  fmap :: fa -> (a -> b) -> f b
{% endvimhl %}

In Python we can use type hints to implement the Functor interface for list.


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

As you can see the implementation of the list Functor is very straight forward. The `fmap` function simply takes a list `fa` and applies the function given in the second argument of `fmap` to every element of the list. As you can see we are now able to apply lambda functions to every list element and chain the results by repeated `fmap` calls. There is also a builtin function in python for `[f(x) for x in fa]` simply called `map`. The same code, using the existing implementation, in Haskell would look like: `(++"0") <$> (show) <$> (+ 1) <$> [1,2,3]`, where `<$>` stands for `fmap` as operator.

# Applicative

Next thing we are going to implement is Applicative. The interface for Applicative in Haskell looks as follows:
{% vimhl hs %}
class Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
{% endvimhl %}

We have to implement two functions. The first one is very simple. Given a type `a` lets say Integer, we simply have to put it into our structure, e.g. `Int -> [Int]`. And the second function states, that given two Applicative, e.g. two lists, and one containing a list with a function, we simply apply the functions of that list to every element of the other list.


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

This is very similar to the implementation of Applicative for lists in Haskell `fs <*> xs = [f x | f <- fs, x <- xs]` and `[(++"0")] <*> ([(show)] <*> ([(+ 1)] <*> [1,2,3]))` yields the same result.

# Monad

The Monad interface requires us to implement two functions. The `return` is very similar to `pure`, we just have to lift a value into the Monad, e.g. put a value into a list. The second function `>>=` also called bind, takes a function that converts an `a` to `m b` e.g. from `a -> [b]` in case of lists.

{% vimhl hs %}
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b
{% endvimhl %}


{% vimhl py %}
class MonadList(ApplicativeList):

    def ret(a) -> m[a]:
        return MonadList(a)

    def __rshift__(xs, f: (a, m[b])) -> m[b]:
        return MonadList(concat (map(f, xs)))

print(
  "MonadList\n",
  MonadList([1, 2, 3])
    >> (lambda x: [x + 1])
    >> (lambda x: [str(x)])
    >> (lambda x: [x + "0"])

# Result: ['20', '30', '40']
{% endvimhl %}


Now lets compare our Python list Monad implementation with the Haskell implementation.

{% vimhl hs %}
instance Monad [] where
  return :: a -> m a
  return x = [x]

  (>>=) :: m a -> (a -> m b) -> m b
  xs >>= f = concat (map f xs)
{% endvimhl %}

As we can see the implementation is very similar, the bind function consists of `concat` and `map`, also called `flatmap`. And this is how we can use the monadic bind function in Haskell `[1,2,3] >>= \x -> [(x+1)] >>= \x -> [(show x)] >>= \x -> [x ++ "0"]`. Here you can find the full implementation of Functor, Applicative and Monad for list in Python:
https://gist.github.com/madnight/b0ae13f7908641655da688ebe7de22cb


## References
[^1]: [getEnv](https://hackage.haskell.org/package/base-4.17.0.0/docs/System-Environment.html#v:getEnv)
[^2]: [In what sense is the IO Monad pure?](https://stackoverflow.com/a/4066401)
