A small, incomplete, and **inconsistent** formalization of homotopy type theory in Idris. This demonstrates that any attempt to formalize HoTT in Idris will be unsound under Idris's current pattern-matching rules.

The issue is that Idris has full dependent pattern matching, without the special restriction to avoid inconsistency with univalence. Using this, one can (and the Idris prelude does) define substitution by heterogeneous equality. This inconsistency with univalence is demonstrated in `Bad.idr` by deriving a contradiction from a proof of `True = False`. More directly, it is possible to define rule K, as shown in `K.idr`.

`Hott.idr` is the main file. It contains the definition of paths, fibers, equivalence, and univalence. `Bad.idr` contains the contradiction. `K.idr` contains a definiton of rule K accepted by Idris.


postulated_identity
-------------------

In the sub-directory 'postulated' I attempt to develop and understand univalence in Idris by defining an identity type without pattern-matching. Is that enough to prevent a contradiction? At the very least the contradiction might have to be derived in some different way.

'Hott.idr' contains a very incomplete reproduction of all the definitions and proofs in the original Hott.idr in the base directory.

'UnivalenceFromScratch.idr' contains an Idris realisation of the definitions in "Univalence From Scratch" by Martin Escardo, which the author describes as "A self-contained, brief and complete formulation of Voevodsky's Univalence Axiom".

'K.idr' contains the statement of Streicher's K axiom, as in 'K.idr' in the base directory, with the proof waiting to be
completed.
