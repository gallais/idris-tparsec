module Examples.JSON

import Language.JSON.Data
import TParsec
import TParsec.Combinators.JSON
import TParsec.Running

%default total

json : String -> Type
json txt = parseType {p = sizedtok Char} txt JSON.value

Empties : Type
Empties = json "{ \"obj\" : {}, \"arr\": [] }"

empties : Empties
empties = MkSingleton $
  JObject [ ("obj", JObject [])
          , ("arr", JArray [])
          ]

Numbers : Type
Numbers = json "[1  ,2.4,   5E2,0.0  ,  1.0e-1 , 0.0256e+2 ] "

numbers : Numbers
numbers = MkSingleton $
  JArray [ JNumber 1
         , JNumber 2.4
         , JNumber 500
         , JNumber 0
         , JNumber 0.1
         , JNumber 2.56
         ]

Booleans : Type
Booleans = json "{ \"false\": false   , \"true\"   : true}"

booleans : Booleans
booleans = MkSingleton $
  JObject [ ("false", JBoolean False)
          , ("true", JBoolean True)
          ]

Strings : Type
Strings = json "{ \"strings\" : [\"A string with \\\" an escaped quote\", \"Another string\"] }"

strings : Strings
strings = MkSingleton $
  JObject [ ("strings", JArray [ JString "A string with \" an escaped quote"
                               , JString "Another string"
                               ])
          ]
