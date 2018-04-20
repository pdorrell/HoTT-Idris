
module Hott.K
import Hott

-- fine:
J : (P : (a,b:t) -> (a~~b) -> Type) ->
    ((a:t) -> P a a Reffl) ->
    ((a,b:t) -> (p:a~~b) -> P a b p)
J P h a a Reffl = h a

-- not fine:
K : (P : (a:t) -> (a~~a) -> Type) ->
    ((a:t) -> P a Reffl) ->
    ((a:t) -> (p:a~~a) -> P a p)
K P h a Reffl = h a

