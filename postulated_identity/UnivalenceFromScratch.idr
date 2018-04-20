
module UnivalenceFromScratch

%access public export
infix 40 ~~

-- define a version of MLTT identity type without giving a constructor

postulate (~~) : t -> t -> Type
postulate refl_ : (a:t) -> a ~~ a

postulate J : (P : (a,b:t) -> (a~~b) -> Type) ->
    ((a:t) -> P a a (refl_ a)) ->
    ((a,b:t) -> (p:a~~b) -> P a b p)
    
-- cf the pattern-matching version with a constructor (as in Hott.idr & K.idr):

--  data (~~) : t -> t -> Type where
--    Reffl : a ~~ a 
--
--  refl_ : (a:t) -> a ~~ a
--  refl_ x = Reffl {a=x}
--
-- J : (P : (a,b:t) -> (a~~b) -> Type) ->
--     ((a:t) -> P a a Reffl) ->
--     ((a,b:t) -> (p:a~~b) -> P a b p)
-- J P H a a Reffl = H a

-- These two proofs show that the postulated '~~' identity type is equivalent
-- in what it implies as the builtin Idris '=' identity type.

eq_implies_native_eq : {x,y : t} -> x ~~ y -> x = y
eq_implies_native_eq {x} {y} x_is_y = J A f x y x_is_y $ x_is_y
  where 
    A : (x, y : t) -> (x ~~ y) -> Type
    A x y x_is_y = x ~~ y -> x = y

    f : (x : t) -> A x x (refl_ x)
    f x _ = Refl
  
native_eq_implies_eq : {x,y : t} -> x = y -> x ~~ y
native_eq_implies_eq {x} x_native_eq_y = rewrite sym x_native_eq_y in refl_ x
 
-- The following code is derived from "Univalence From Scratch" by Martin Escardo
-- http://www.cs.bham.ac.uk/~mhe/agda-new/UnivalenceFromScratch.html (17 Mar 2018)

is_singleton : (t : Type) -> Type
is_singleton t = (c : t ** ((x : t) -> c ~~ x))

fiber : {xt : Type} -> {yt : Type} -> (f : xt -> yt) -> (y : yt) -> Type
fiber {xt} {yt} f y = (x : xt ** f x ~~ y)

is_equivalence : {xt : Type} -> {yt : Type} -> (f : xt -> yt) -> Type
is_equivalence {xt} {yt} f = (y : yt) -> is_singleton (fiber f y)

equivalences : (xt : Type) -> (yt : Type) -> Type
equivalences xt yt = (f : (xt -> yt) ** is_equivalence f)

singleton_type : {xt : Type} -> (x : xt) -> Type
singleton_type {xt} x = (y : xt ** y ~~ x)

nu : {xt : Type} -> (x : xt) -> singleton_type x
nu x = (x ** refl_ x)

phi : {xt : Type} -> (y, x : xt) -> (p : y ~~ x) -> nu x ~~ (y ** p)
phi = J A f
  where
    A : {xt : Type} -> (y : xt) -> (x : xt) -> (p : y ~~ x) -> Type
    A y x p = nu x ~~ (y ** p)

    f : {xt : Type} -> (x : xt) -> A x x (refl_ x)
    f x = refl_ (nu x)
    
g : {xt : Type} -> (x : xt) -> (sigma : singleton_type x) -> (nu x ~~ sigma)
g x (y ** p) = phi y x p

h : {xt : Type} -> (x : xt) -> (c : singleton_type x ** ((sigma : singleton_type x) -> c ~~ sigma))
h x = (nu x ** g x)

singleton_types_are_singletons: {xt : Type} -> (x : xt) -> is_singleton (singleton_type x)
singleton_types_are_singletons x = h x

-- like id, but the Type parameter is explicit
id_ : (xt : Type) -> xt -> xt
id_ xt x = x

is_singleton_fiber_of_id : (xt : Type) -> (y : xt) -> is_singleton (fiber (id_ xt) y)
is_singleton_fiber_of_id xt y = singleton_types_are_singletons y

id_is_equiv : (xt : Type) -> is_equivalence (id_ xt)
id_is_equiv xt y = is_singleton_fiber_of_id xt y

id_to_eq : (xt : Type) -> (yt : Type) -> xt ~~ yt -> equivalences xt yt
id_to_eq = J A f
  where
    A : (xt : Type) -> (yt : Type) -> xt ~~ yt -> Type
    A xt yt p = equivalences xt yt

    f : (xt : Type) -> equivalences xt xt
    f xt = (id_ xt ** id_is_equiv xt)


-- Finally, we can postulate Univalence
--
-- (Note: Universes are implicit in Idris, so we can't say "The Universe U is Univalent")

IsUnivalent : Type
IsUnivalent = (xt : Type) -> (yt : Type) -> is_equivalence (id_to_eq xt yt)

postulate univalence : IsUnivalent

-- TODO: derive a contradiction ...

-- Also TODO: prove a contradiction using the definition of ~~ via Reffl, ie re-deriving
-- the contradiction from Hott.idr.
