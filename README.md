A small, incomplete, and **inconsistent** formalization of homotopy type theory in Idris. This demonstrates that any attempt to formalize HoTT in Idris will be unsound under Idris's current pattern-matching rules.

The issue is that Idris has full dependent pattern matching, without the special restriction to avoid inconsistency with univalence. Using this, one can (and the Idris prelude does) define substitution by heterogeneous equality. This inconsistency with univalence is demonstrated in `Bad.idr` by deriving a contradiction from a proof of `True = False`. More directly, it is possible to define rule K, as shown in `K.idr`.

`Hott.idr` is the main file. It contains the definition of paths, fibers, equivalence, and univalence. `Bad.idr` contains the contradiction. `K.idr` contains a definiton of rule K accepted by Idris.
