
module Hott.K
import Hott

-- fine:
J : (P : (a,b:t) -> (a~~b) -> Type) ->
    ((a:t) -> P a a refl) ->
    ((a,b:t) -> (p:a~~b) -> P a b p)
J P H a a refl = H a

-- not fine:
K : (P : (a:t) -> (a~~a) -> Type) ->
    ((a:t) -> P a refl) ->
    ((a:t) -> (p:a~~a) -> P a p)
K P H a refl = H a

