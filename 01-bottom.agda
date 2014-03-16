module 01-bottom where

-- In Agda, types are theorems, and instances of types are proofs. The
-- simplest theorem is ⊥ (bottom): a theorem which has no proof, and
-- is useful to represent any contradictory situation. We declare ⊥ as
-- an algebraic data type without constructors. If ⊥ has no
-- constructors, then it also has no instances, and thereby perfectly
-- serves our purpose.

data ⊥ : Set where
