---
title: JSON parsing in ELM
date: 2017-01-14
tags: ["ELM", "JSON", "Functional Programming"]
cover: https://i.imgur.com/wOEd1Wy.jpg
---

# Intro
There is a ongoing hype of JavaScript[^1] in the developer community. Virtually everything is now compiled to JavaScript and delivered to the client. JavaScript is also becoming very popular for server side development[^2], replacing Ruby and PHP as primary programming language. Not only that, there's also an ongoing serverless trend, moving most of the back-end code into the front-end part of the application.[^3] This paradigm shift results in highly complex front-end applications, making it very complicated to write these application with plain old vanilla JavaScript. Therefore the community started to put much effort in improving the JavaScript front-end development. They published a new JavaScript Standard ES6 (ECMAScript 2015). They created the Babel compiler to compile that new standard to vanilla JavaScript allowing it's execution in older browsers. They invented frameworks and tools like react, webpack, karma, mocha, enzyme, gulp, eslint and many more to make the life as JavaScript developer as comfortable as possible.[^5] It takes many weeks to get familiar with these tools, but the benefits will pay off in the long run. Following all the current best practices leads to a setup with many different tools and a highly improved JavaScript syntax, that basically follows the approach of reactive functional programming. It would take a very long time to explain why that is the case - long story short, the main problem is mutable state. Mutable state is not only a potential source of bugs, it is also a one of the top reasons for unpredictable application behavior and is in principle not compatible with parallelization.[^6] For that reason, why not experimenting with a reactive functional programming language explicitly designed for front-end programming and compiling to vanilla JavaScript.

# ELM
ELM is a static typed, reactive, pure functional programming language. It has a simplified Haskell syntax, making it much easier to use than Haskell. It is focused on front-end web development and therefore compiles to JavaScript. It has the builtin features of react and redux.[^7]

### WORK IN PROGRESS ... MORE SOON

<!-- ### WIP
```elm
import Html exposing (..)
import Http
import Json.Decode exposing (..)

type alias ProgrammingLanguage = {
  name : String,
  year : String,
  quarter: String,
  count : String
}

type alias Model =
  {
    languageList : List ProgrammingLanguage
  }

type Msg =
  MorePlease | NewLang (Result Http.Error (List ProgrammingLanguage))

main : Program Never Model Msg
main = Html.program
    {
      init = init
    , view = view
    , update = update
    , subscriptions = subscriptions
    }

emptyList : List ProgrammingLanguage
emptyList = [ { name = "", year = "", quarter = "", count = "" } ]

init : (Model, Cmd Msg)
init = (Model emptyList, getProgrammingLanguages)

update : Msg -> Model -> (Model, Cmd Msg)
update msg model =
  case msg of
    MorePlease ->
      (model, getProgrammingLanguages)
    NewLang (Ok newUrl) ->
      (Model newUrl, Cmd.none)
    NewLang (Err _) ->
      (model, Cmd.none)

toHtmlList : List ProgrammingLanguage -> Html msg
toHtmlList strings =
  ul [] (List.map toLi strings)

toLi : ProgrammingLanguage -> Html msg
toLi lang =
  li [] [ text (
  lang.name ++ " " ++
  lang.year ++ " " ++
  lang.quarter ++ " " ++
  lang.count )]

view : Model -> Html Msg
view model =
  toHtmlList model.languageList

subscriptions : Model -> Sub Msg
subscriptions model =
  Sub.none

getProgrammingLanguages : Cmd Msg
getProgrammingLanguages =
  let url = "http://localhost:23322/test123.json"
  in Http.send NewLang (Http.get url langListDecoder)

langDecoder: Decoder ProgrammingLanguage
langDecoder = map4 ProgrammingLanguage
    (field "name" string)
    (field "year" string)
    (field "quarter" string)
    (field "count" string)

langListDecoder : Decoder (List ProgrammingLanguage)
langListDecoder = Json.Decode.list langDecoder
``` -->

[^1]: Programming Languages Github Ranking https://madnight.github.io/githut
[^2]: https://en.wikipedia.org/wiki/Node.js
[^3]: What is Serverless Architecture? https://medium.com/@PaulDJohnston/what-is-serverless-architecture-43b9ea4babca#.5adec3yz0
[^4]: Destructuring: What, Why and How - Part 1 of ES6 JavaScript Features https://www.youtube.com/watch?v=PB_d3uBkQPs
[^5]: Boilerplate Example react-webpack-babel-karma-boilerplate
https://github.com/madnight/react-webpack-babel-karma-boilerplate
[^6]: So You Want to be a Functional Programmer https://medium.com/@cscalfani/so-you-want-to-be-a-functional-programmer-part-1-1f15e387e536#.wu667z5wl
[^7]: Redux is influenced by ELM https://github.com/reactjs/redux#Influences
