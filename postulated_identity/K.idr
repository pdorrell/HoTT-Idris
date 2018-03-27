
module Hott.K

-- This matches the proof of axiom K in K.idr in the base directory, 
-- but I avoid defining the Reffl constructor for the "~~" identity type.
--
-- Question: can we still prove K?

%access public export

infix 40 ~~
infix 40 ~=

postulate (~~) : t -> t -> Type

postulate refl_ : (a:t) -> a ~~ a

postulate J : (P : (a,b:t) -> (a~~b) -> Type) ->
    ((a:t) -> P a a (refl_ a)) ->
    ((a,b:t) -> (p:a~~b) -> P a b p)

K : (P : (a:t) -> (a~~a) -> Type) ->
    ((a:t) -> P a (refl_ a)) ->
    ((a:t) -> (p:a~~a) -> P a p)
K P h a p = ?hole
