---
title: JSON parsing in ELM
date: 2017-01-14
tags: ["ELM", "JSON", "Functional Programming"]
cover: https://i.imgur.com/w21f4XF.png
---

There is a ongoing hype of [JavaScript](https://madnight.github.io/githut) in the programmer community. Virtually everything is now compiled to JavaScript and delivered to client executing it with e.g. Googles V8 engine.

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
```
