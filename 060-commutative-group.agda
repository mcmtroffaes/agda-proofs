module 060-commutative-group where

-- We need groups.

open import 050-group

record CommutativeGroup
  {M : Set}
  (_==_ : M -> M -> Set)
  (_*_ : M -> M -> M)
  (id : M)
  (invert : M -> M)
  : Set1 where

  field
    group : Group _==_ _*_ id invert
    comm : ∀ {r s} -> (r * s) == (s * r)

  open Group group public

  -- Nothing proven here yet.
