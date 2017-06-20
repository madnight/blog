---
title: JSON parsing in ELM
date: 2017-01-14
tags: ["ELM", "JSON", "Functional Programming"]
subtitle: JSON parsing in a purely functional web language
cover: https://i.imgur.com/wOEd1Wy.jpg
---

# Immutable state of the art
There is a ongoing hype of JavaScript[^1] in the developer community. Virtually everything is now compiled to JavaScript and delivered to the client. JavaScript is also becoming very popular for server side development[^2], replacing Ruby and PHP as primary programming language.[^9] Not only that, there's also an ongoing serverless trend, moving most of the back-end code into the front-end part of the application.[^3] This paradigm shift results in highly complex front-end applications, making it very complicated to write these application with plain old vanilla JavaScript. Therefore the community started to put much effort in improving the JavaScript front-end development. They published a new JavaScript Standard ES6 (ECMAScript 2015). They created the Babel compiler to compile that new standard to vanilla JavaScript allowing it's execution in older browsers. They invented frameworks and tools like react, webpack, karma, mocha, enzyme, gulp, eslint and many more to make the life as JavaScript developer as comfortable as possible.[^5]


It takes many weeks to get familiar with these tools, but the benefits will pay off in the long run. Following all the current best practices leads to a setup with many different tools and a highly improved JavaScript syntax, that basically follows the approach of reactive functional programming. It would take a very long time to explain why that is the case - long story short, the main problem is mutable state.[^8] Mutable state is not only a potential source of bugs, it is also a one of the top reasons for unpredictable application behavior and is in principle not compatible with parallelization.[^6] For that reason, why not experimenting with a reactive functional programming language explicitly designed for front-end programming and compiling to vanilla JavaScript.

# Parse JSON in Elm 0.18
Elm is a static typed, reactive, pure functional programming language. It has a simplified Haskell syntax, making it much easier to use than Haskell. It is focused on front-end web development and therefore compiles to JavaScript. It has the builtin features of react and redux.[^7]

Lets consider an JSON API in the following format:

```Json
[
  {
    "name": "JavaScript",
    "year": "2012",
    "quarter": "2",
    "count": "118009"
  },
  {
    "name": "Ruby",
    "year": "2012",
    "quarter": "2",
    "count": "67773"
  },
  {
    "name": "Python",
    "year": "2012",
    "quarter": "2",
    "count": "42212"
  }
]
```
Since Elm is strongly typed we have to create a type that matches the given JSON objects.
```elm
type alias ProgrammingLanguage = {
  name : String,
  year : Int,
  quarter: Int,
  count : Int
}
```
As you can see the attribute name is a string and year, quarter, count are integers. The JSON API provides integers encoded as strings, so it is necessary to do a type cast. Therefore we need to write a simple custom decoder, that converts a string to integer.

```elm
stringAsInt : Decoder Int
stringAsInt = string |> andThen (String.toInt >> fromResult)
```
Lets take a look at the type definition to see how this works.
`andThen : (a -> Decoder b) -> Decoder a -> Decoder b`
The function `andThen` takes two arguments a decoder a, in this case the standard string decoder and a type cast function from a to decoder b that converts the result of our string decoder to an new decoder of type b. This procedure is a simple chain, first decode as string and then decode as int by type conversion. If you know Haskell `andThen` is the equivalent of `(=<<) :: Monad m => (a -> m b) -> m a -> m b` the monadic bind that sequentially compose two actions by passing any value produced by the first as an argument to the second. If you are not familiar with the pipe `|>` and function composition `>>` notation you can also write the function with as a lambda expression `andThen (\n -> fromResult(String.toInt(n))) string`. Now we are able to use that decoder to decode a single JSON object.
```elm
langDecoder : Decoder ProgrammingLanguage
langDecoder =
  map4 ProgrammingLanguage
    (field "name" string)
    (field "year" stringAsInt)
    (field "quarter" stringAsInt)
    (field "count" stringAsInt)
```
Since our API is a list of programming language objects we need to parse the whole list. `Json.Decode.list : Decoder a -> Decoder (List a)`
```elm
langListDecoder : Decoder (List ProgrammingLanguage)
langListDecoder = Json.Decode.list langDecoder
```
Finally you are able to use the decoder to parse JSON from a given URL `Http.get url langListDecoder`
```elm
getProgrammingLanguages : Cmd Msg
getProgrammingLanguages =
  let url = "gh-star-event.json"
  in Http.send NewLang (Http.get url langListDecoder)
```
```javascript
var foo = function(x) {
  return(x + 5);
}
foo(3)
```
See https://github.com/madnight/elm-webpack-starter for a full working API parsing example.

## Update 

There's a new command line tool and website https://github.com/eeue56/json-to-elm that allows for automatic conversion of JSON to elm code.

> This project allows you to automate the creation of:
>
> * type aliases from JSON data
> * decoders from type aliases and some union types
> * encoders from type aliases and some union types


## References
[^1]: [Programming Languages Github Ranking](https://madnight.github.io/githut)
[^2]: [Event-driven I/O server-side JavaScript environment based on V8](https://en.wikipedia.org/wiki/Node.js)
[^3]: [What is Serverless Architecture?](https://medium.com/@PaulDJohnston/what-is-serverless-architecture-43b9ea4babca#.5adec3yz0)
[^4]: [Destructuring: What, Why and How - Part 1 of ES6 JavaScript Features]( https://www.youtube.com/watch?v=PB_d3uBkQPs)
[^5]: [Boilerplate Example react-webpack-babel-karma-boilerplate](https://github.com/madnight/react-webpack-babel-karma-boilerplate)
[^6]: [So You Want to be a Functional Programmer]( https://medium.com/@cscalfani/so-you-want-to-be-a-functional-programmer-part-1-1f15e387e536#.wu667z5wl)
[^7]: [Redux is influenced by ELM](https://github.com/reactjs/redux#Influences)
[^8]: [How can you do anything useful without mutable state?]( http://stackoverflow.com/questions/1020653/how-can-you-do-anything-useful-without-mutable-state)
[^9]: [JavaScript more widely used in industry than PHP or Ruby](http://www.tiobe.com/tiobe-index/)
