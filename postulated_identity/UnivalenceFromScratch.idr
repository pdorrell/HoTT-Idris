module UnivalenceFromScratch

%default total
%access public export
infix 40 ~~

-- define a version of MLTT identity type without giving a constructor

postulate (~~) : t -> t -> Type
postulate refl_ : (a:t) -> a ~~ a

postulate J : (P : (a,b:t) -> (a~~b) -> Type) ->
    ((a:t) -> P a a (refl_ a)) ->
    ((a,b:t) -> (p:a~~b) -> P a b p)
    
postulate J_refl : (P : (a,b:t) -> (a~~b) -> Type) ->
    (p_for_refl: (a:t) -> P a a (refl_ a)) -> 
    (a: t) -> J P p_for_refl a a (refl_ a) ~~ p_for_refl a
    
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

eq_implies_native_eq : {t : Type} -> {x,y : t} -> x ~~ y -> x = y
eq_implies_native_eq {t} {x} {y} x_is_y = J A f x y x_is_y $ x_is_y
  where 
    A : (x, y : t) -> (x ~~ y) -> Type
    A x y x_is_y = x ~~ y -> x = y

    f : (x : t) -> A x x (refl_ x)
    f x _ = Refl
  
native_eq_implies_eq : {x,y : t} -> x = y -> x ~~ y
native_eq_implies_eq {x} x_native_eq_y = rewrite sym x_native_eq_y in refl_ x

-- Lemmas about dependent pairs
 
dpair_lemma : {t : Type} -> {P : t -> Type} -> {x : t} -> {y1, y2 : P x} -> (x ** y1) = (x ** y2) -> y1 = y2
dpair_lemma {P} {x} {y1 = y2} {y2 = y2} Refl  = Refl

dpair_eq_lemma : {t : Type} -> {P : t -> Type} -> {x : t} -> {y1, y2 : P x} -> (x ** y1) ~~ (x ** y2) -> y1 ~~ y2
dpair_eq_lemma {t} {P} {x} {y1} {y2} x_y1_eq_x_y2 = 
  let x_y1_native_eq_x_y2 = eq_implies_native_eq {t = DPair t P} {x=(x**y1)} {y=(x**y2)} x_y1_eq_x_y2
      y1_native_eq_y2 = dpair_lemma x_y1_native_eq_x_y2
  in native_eq_implies_eq y1_native_eq_y2

-- Direct proofs of symm & tran & congg and transport (or we could have gone via the 'native_eq' lemmas ...)
 
symm : a ~~ b -> b ~~ a
symm {a} {b} a_is_b = 
  let f = J symm_P symm_P_for_refl
      f2 = the (a~~b -> b~~a) $ f a b a_is_b
    in f2 a_is_b
  where 
     symm_P : (a,b:t) -> (a~~b) -> Type
     symm_P a b x = a ~~ b -> b ~~ a

     symm_P_for_refl : (a:t) -> symm_P a a (refl_ a)
     symm_P_for_refl a = the (a ~~ a -> a ~~ a) $ id
     
infixl 50 @-
(@-) : a ~~ b -> b ~~ c -> a ~~ c
(@-) {a} {b} {c} a_is_b = 
  let f = J (trans_P c) (trans_P_for_refl c)
      f2 = the (a ~~ b -> b ~~ c -> a ~~ c) $ f a b a_is_b
    in f2 a_is_b
  where
     trans_P : (c : t) -> (a,b:t) -> (a~~b) -> Type
     trans_P c a b x = a ~~ b -> b ~~ c -> a ~~ c

     trans_P_for_refl : (c : t) -> (a:t) -> trans_P c a a (refl_ a)
     trans_P_for_refl c a x = the (a ~~ c -> a ~~ c) $ id

tran : a ~~ b -> b ~~ c -> a ~~ c
tran = (@-)

congg_P : {t : Type} -> (a, b : t) -> (a ~~ b) -> Type
congg_P {t} a b p = {t2 : Type} -> (f: t -> t2) -> (a ~~ b) -> f a ~~ f b
  
congg : {t : Type} -> {a,b: t} -> {t2 : Type} -> {f: t -> t2} -> (a ~~ b) -> f a ~~ f b
congg {t} {a} {b} {t2} {f} p = J {t} congg_P congg_for_refl_a a b p f p
  where
    congg_for_refl_a : {t : Type} -> (a : t) -> (congg_P {t} a a (refl_ a))
    congg_for_refl_a a f p = refl_ (f a)
    
transport_P : {t : Type} -> (a, b : t) -> a ~~ b -> Type
transport_P {t} a b p = (P : t -> Type) -> P a -> P b

transport : {t : Type} -> (a, b : t) -> a ~~ b -> (P : t -> Type) -> P a -> P b
transport {t} a b a_eq_b P p_a = J {t} transport_P transport_for_refl_a a b a_eq_b P p_a
  where
    transport_for_refl_a : {t : Type} -> (a : t) -> (transport_P {t} a a (refl_ a))
    transport_for_refl_a a _ = id

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

-- h-propositions and h-sets ...

is_prop : (t : Type) -> Type
is_prop t = (a : t) -> (b : t) -> a ~~ b

is_set : (t : Type) -> Type
is_set t = (a : t) -> (b : t) -> is_prop (a ~~ b)

-- Unfortunately the following theorems are incompatible with Univalence ...

every_type_is_set : (t : Type) -> is_set t
every_type_is_set t x y p q = 
  let (y_singleton ** equate_to_y_singleton) = singleton_types_are_singletons y
      xp_equated = equate_to_y_singleton (x ** p)
      xq_equated = equate_to_y_singleton (x ** q)
      symm_xp_equated = symm {a=y_singleton} {b=(x ** p)} xp_equated
      xp_xq_equated = tran {a=(x ** p)} {b=y_singleton} {c=(x ** q)} symm_xp_equated xq_equated
      p_eq_q = the (p ~~ q) $ dpair_eq_lemma xp_xq_equated
  in p_eq_q
  
UIP : {t : Type} -> {a,b : t} -> (p, q : a~~b) -> p~~q
UIP {t} {a} {b} p q = every_type_is_set t a b p q

all_self_identities_eq_to_refl : {t : Type} -> {a : t} -> (p : a ~~ a) -> p ~~ (refl_ a)
all_self_identities_eq_to_refl {t} {a} p = UIP {t} {a=a} {b=a} p (refl_ a)

K : (P : (a:t) -> (a~~a) -> Type) ->
    ((a:t) -> P a (refl_ a)) ->
    ((a:t) -> (p:a~~a) -> P a p)
K P h a p = 
   let h_of_a = h a
       p_eq_refl_a = all_self_identities_eq_to_refl {t} {a} p
       refl_a_eq_p = the ((refl_ a) ~~ p) $ symm p_eq_refl_a
   in transport (refl_ a) p refl_a_eq_p (P a) h_of_a

-- TODO show contradiction of K and Univalence ...
