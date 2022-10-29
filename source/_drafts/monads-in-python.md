---
title: Monads in Python
date: 2022-10-29
tags: ["python", "haskell", "monads", "functional programming"]
subtitle: Functor, Applicative, Monads in Python
---

I this post I show you an instance of Functor, Applicative and Monad in Python for Lists.

# Functor

This is how a Functor in Haskell looks like. Althougt it is named class in Haskell you can think of it as an interface. This interface states that in order for something to be a Functur it has to implement the fmap (or map) function. A Functor is also called "mappable", because it is something we can map over like a List.
```haskell
class Functor f where
  fmap :: fa -> (a -> b) -> f b
```

In Python we can use type hints to implement a List Functor type.

```python
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
```

As you can see the imlemtation of the List Functor is very straight forward. The fmap function simply takes a list fa and applies the function given in the second argument of fmap to every element of the list. As you can see we are now able to apply lambda functions to every list element and chain the results by repeated fmap calls. There is also a builtin function in python for `[f(x) for x in fa]` simply called `map`.

```python


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

```

In JavaScript:
```js
for (i=0; i < 4; i++)
    console.log(i)
```

In Haskell:
```haskell
forM_ [0..3] $ \i ->
    print i
```

Result:
```
0
1
2
3
```

The similarities are quiet obvious and none of these snippets is more or less complex than the others. One should note that the `for` in Python and JavaScript are native language keywords, whereas the Haskell version `forM_` is a function.

# While True with Sleep

One common task in programming is to create endless loops that does something and then sleeps for a while and repeat. The following example implements a `while` true loop and logs the current date to a temporary file.

In Python:
```python
while True:                                           # endless loop
    now = datetime.datetime.utcnow().isoformat()      # timestamp
    with open('/tmp/times.txt', 'a') as file:         # open file
        file.write(now + "\n")                        # write file
    time.sleep(2)                                     # sleep 2 seconds
```

In JavaScript:
```javascript
while(true) {                                         // endless loop
    let now = new Date().toISOString()                // timestamp
    fs.appendFileSync("/tmp/times.txt", now + "\n");  // write file
    await new Promise(done => setTimeout(done, 2000)) // sleep 2 seconds
}
```

In Haskell:
```haskell
forever $ do                                           -- endless loop
    now <- getCurrentTime                              -- timestamp
    appendFile "/tmp/times.txt" $ show now ++ "\n"     -- write file
    threadDelay $ 2 * 1000 * 1000                      -- sleep 2 seconds
```

Result:
```sh
$ cat /tmp/timestamps.txt
2018-08-23T20:09:22.553Z
2018-08-23T20:09:24.556Z
2018-08-23T20:09:26.558Z
...
```

Please note that in order to use the `await` keyword in JavaScript it is necessary to put it in an `async` function. I omitted this kind of extra "noise" to make the syntax comparisons of the `while` loop more clear. I also removed the import statements for Python and Haskell. Haskells `main` function is also ommited. As we can see there is not much difference between the code examples. The Haskell versions of doing I/O (reading time, writing to file and sleep) is syntactically the shortest one. Of course high expressivenesses, and thus fewer lines of code, does not imply simplicity. A language that is very terse tend to be more complex to understand. That is because it requires the programmer to know the meaning of different short names, standard functions and operators.

# Nested Loop over 2D List

In Python:
```python
# list declaration
list2D = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]

for x in range(len(list2D)):                       # outer loop
    for y in range(len(list2D[x])):                # inner loop
      list2D[x][y] = 42                            # mutate list at x,y

print(list2D)                                      # print list
```

In JavaScript:
```javascript
// list declaration
let list2D = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]

for (x=0; x < list2D.length; x++)                  // outer loop
   for (y=0; y < list2D[x].length; y++)            // inner loop
        list2D[x][y] = 42                          // mutate list at x,y

console.log(list2D)                                // print list
```

In Haskell:
```haskell
 -- list delcaration
let list2D = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]

print $ runST $ do                                 -- print and run state

  listState <- (mapM . mapM) newSTRef list2D       -- create list state

  forM_ [0..length list2D-1] $ \x ->               -- outer loop
      forM_ [0..length (list2D !! x)-1] $ \y ->    -- inner loop
          writeSTRef (listState !! x !! y) 42      -- mutate list state at x,y

  (mapM . mapM) readSTRef listState                -- read (return) state
```

Result:
```
[[42,42,42,42],[42,42,42,42],[42,42,42,42]]
```

As we can see modifying the state of a list is a bit more complex (requires more syntax) in Haskell than in Python or JavaScript. The benefits of this additional syntax in Haskell is that the State is fully encapsulated in the State Monad which makes this computation absolutely pure.[^1] This is similar to frameworks like react + redux where you modify the state in a pure manner, but natively available in Haskell and considered default for state manipulation.

The code snippets shows the similarities between the languages. Given the fact that it's not necessary to develop an deep understanding for mathematical concepts from category theory for e.g. Functor or Monoid, then Haskell can be seen as a nice strongly typed and purely functional programming language with many similarities to scripting languages like JavaScript or Python. So one approach is to learn Haskell in an imperative, pure, functional style and simply ignore the higher concepts of the language until you are either really interested in them or you think you need it.

## References
[^1]: [Purity of runST is finally proven](https://www.reddit.com/r/haskell/comments/679jd3/purity_of_runst_is_finally_proven)
