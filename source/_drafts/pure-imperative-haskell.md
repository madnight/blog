---
title: Pure Imperative Haskell
date: 2018-08-22
tags: ["elm", "json", "functional programming"]
subtitle: Pure Imperative Code Examples in Haskell
---

# Iterative FOR Loops

In Python:
```python
for i in range(10):
    print(i)
```

In JavaScript:
```js
for (i=0; i < 10; i++)
    console.log(i)
```

In Haskell:
```haskell
forM_ [0..9] $ \i ->
    print i
```

Result:
```
0
1
2
3
4
5
6
7
8
9
```

# Nested Loop over 2D List

In Python:
```python
list2D = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]

for x in range(len(list2D)):
    for y in range(len(list2D[0])):
      list2D[x][y] = 42

print(list2D)
```


In JavaScript:
```javascript
let list2D = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]

for (x=0; x < list2D.length; x++)
   for (y=0; y < list2D[0].length; y++)
        list2D[x][y] = 42

console.log(list2D)
```

In Haskell:
```haskell
let list2D = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]

print $ runST $ do

  listState <- (mapM . mapM) newSTRef list2D

  forM_ [0..length list2D-1] $ \x ->
      forM_ [0..length (list2D !! 0)-1] $ \y ->
          writeSTRef (listState !! x !! y) 42

  (mapM . mapM) readSTRef listState
```

Result:
```
[[42,42,42,42],[42,42,42,42],[42,42,42,42]]
```

As we can see modifying the state of a list is a bit more complex (requires more syntax) in Haskell than in Python or JavaScript. The benefits of this additional syntax in Haskell is that the State is fully encapsulated in the State Monad which makes this compuation absolutley pure.[^1] This is similar to frameworks like react + redux where you modify the state in a pure manner, but nativley available in Haskell without extra dependencies and used as the default way for state manipulation.


## References
[^1]: [Purity of runST is finally proven](https://www.reddit.com/r/haskell/comments/679jd3/purity_of_runst_is_finally_proven)
