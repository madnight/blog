---
title: Pure Imperative Haskell
date: 2018-08-27
tags: ["haskell", "imperative", "functional programming"]
subtitle: Pure Imperative Code Examples in Haskell
---

It is often said that simple things that matter in the real world are hard to write in Haskell. And indeed it requires a litte bit more syntax to write in an imperative mutating style in Haskell compared to Python or JavaScript.

<center>
<img src="/images/hask-hello.jpg" style="width:500px;">
</center>

 In this post we will compare these three languages with very simple examples and see how much more syntax we need to write in Haskell to do imperative style programming.

# Iterative FOR Loops

Simple for loop with print to `stdout`.

In Python:
```python
for i in range(4):
    print(i)
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

Please note that in order to use the `await` keyword in JavaScript it is necessary to wrap it inside an `async` function. I omitted this extra noise to make the visible syntax comparisons of the `while` loop more clear. I also removed the import statements for Python and Haskell and Haskells `main` function. As we can see there is not much difference between the code examples. The Haskell versions of doing I/O (reading time, writing to file and sleep) is syntactically the shortest one. Of course high expressivenesses, and thus fewer lines of code, does not imply simplicity. A language that is very terse tend to be more complex to understand. That is because it requires the Programmer to know the meaning of different short names, standard functions and operators.


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



As we can see modifying the state of a list is a bit more complex (requires more syntax) in Haskell than in Python or JavaScript. The benefits of this additional syntax in Haskell is that the State is fully encapsulated in the State Monad which makes this computation absolutely pure.[^1] This is similar to frameworks like react + redux where you modify the state in a pure manner, but natively available in Haskell without any extra dependencies and considered as the default way for state manipulation.

The code snippets shows the similarities between the languages. Given the fact that it is not necessary to develop an deep understanding for mathematical concepts from category theory for e.g. Functor or Monoid, then Haskell can be seen as a nice strongly typed and purely functional programming language with many similarities to scripting languages like JavaScript or Python. So one approach is to learn Haskell in an imperative, pure, functional style and simply ignore the higher concepts of the language until you are either really interested in them or you think you need it.


## References
[^1]: [Purity of runST is finally proven](https://www.reddit.com/r/haskell/comments/679jd3/purity_of_runst_is_finally_proven)
