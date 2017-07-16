
module Hott.K
import Hott

-- fine:
J : (P : (a,b:t) -> (a~~b) -> Type) ->
    ((a:t) -> P a a Reffl) ->
    ((a,b:t) -> (p:a~~b) -> P a b p)
J P H a a Reffl = H a

-- not fine:
K : (P : (a:t) -> (a~~a) -> Type) ->
    ((a:t) -> P a Reffl) ->
    ((a:t) -> (p:a~~a) -> P a p)
K P H a Reffl = H a

