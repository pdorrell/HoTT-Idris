
module Hott

-- This is intended to be like Hott.idr in the base directory, 
-- but I avoid defining the Reffl constructor for the "~~" identity type.
--
-- It is not at all complete, because I haven't worked out how to 
-- reproduce all the content of Hott.idr without being able to pattern-match
-- on Reffl.
--
-- (See UnivalenceFromScratch.idr for a simpler development of Univalence
--  which I have been able to code fully in Idris, using the postulated version
--  of the identity type.)
--
-- The big question: does avoid Reffl prevent us from proving a contradiction?

%access public export

infix 40 ~~

postulate (~~) : t -> t -> Type

postulate refl_ : (a:t) -> a ~~ a

postulate J : (P : (a,b:t) -> (a~~b) -> Type) ->
    ((a:t) -> P a a (refl_ a)) ->
    ((a,b:t) -> (p:a~~b) -> P a b p)

lhs : {a:t} -> {b:t} -> a ~~ b -> t
lhs {a} {b} p = a

rhs : {a:t} -> {b:t} -> a ~~ b -> t
rhs {a} {b} p = b

reify : (p : a ~~ b) -> (lhs p ~~ rhs p)
reify p = p

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

-- TODO - define and prove the rest of Hott.idr that is relevant to proving a contradiction

-- This comes from Bad.idr ...

upgrade : a ~~ b -> a = b
upgrade {a} {b} a_is_b =
   let f = J upgrade_P upgrade_P_for_refl
       f2 = the (a ~~ b -> a = b) $ f a b a_is_b
    in f2 a_is_b
   where
     upgrade_P : (a,b:t) -> (a~~b) -> Type
     upgrade_P a b x = a ~~ b -> a = b

     upgrade_P_for_refl : (a:t) -> upgrade_P a a (refl_ a)
     upgrade_P_for_refl a a_is_a = Refl
