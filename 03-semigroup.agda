module 03-semigroup where

-- We have contradiction and equivalence.

open import 02-equivalence public

-- Semigroups are basically a set with equality and some binary
-- operator which is associative and respects equality.

record SemiGroup
  {M : Set}
  (_==_ : M -> M -> Set)
  (_*_ : M -> M -> M)
  : Set1 where

  field
    equiv : Equivalence _==_
    assoc : ∀ {r s t} -> ((r * s) * t) == (r * (s * t))
    cong : ∀ {r s u v} -> (r == s) -> (u == v) -> (r * u) == (s * v)

  -- The next line brings all fields and declarations of Equivalence
  -- into this record's namespace so we can refer to them in an
  -- unqualified way in proofs (for example, we can write "refl" for
  -- "Equivalence.symm equiv" and so on).

  open Equivalence equiv public

  -- No theorems here yet.
