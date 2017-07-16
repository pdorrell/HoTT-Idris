
module Hott.Bad
import Hott
import Data.So

upgrade : a ~~ b -> a = b
upgrade Reffl = Refl

super_upgrade : (p : a ~~ b) -> (rw p x ~~ y) -> x = y
super_upgrade Reffl Reffl = Refl

not_not : (x:Bool) -> not (not x) ~~ x
not_not False = refl_ False
not_not True = refl_ True

not_iso : Iso Bool Bool
not_iso = MkIso not not not_not not_not

not_eq : Bool ~= Bool
not_eq = iso_to_eq not_iso

not_path : Bool ~~ Bool
not_path = eq_to_path not_eq

rw_not_True : rw Hott.Bad.not_path True ~~ False
rw_not_True = rw_eqpath not_eq True

True_is_False : True = False
True_is_False = super_upgrade not_path rw_not_True

implementation Uninhabited (True = False) where
  uninhabited p = uninhabited (replace p Oh)

contradiction : a
contradiction = absurd True_is_False

