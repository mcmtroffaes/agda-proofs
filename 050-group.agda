module 050-group where

-- We need monoids.

open import 040-monoid

-- A group is a monoid where every element has an inverse. This is
-- equivalent to saying that we have a function mapping every element
-- to an inverse of that element: this function is called "invert"
-- below.

record Group
  {M : Set}
  (_==_ : M -> M -> Set)
  (_*_ : M -> M -> M)
  (id : M)
  (invert : M -> M)
  : Set1 where
  field
    monoid : Monoid _==_ _*_ id
    icong : ∀ {r s} -> (r == s) -> (invert r) == (invert s)
    r*ir==id : ∀ {r} -> (r * (invert r)) == id
    ir*r==id : ∀ {r} -> ((invert r) * r) == id

  open Monoid monoid public

  -- Trivial but useful equalities.
  id==r*ir : ∀ {r} -> id == (r * (invert r))
  id==r*ir = symm r*ir==id
  id==ir*r : ∀ {r} -> id == ((invert r) * r)
  id==ir*r = symm ir*r==id

  -- Double inverse gets back original.
  iir==r : ∀ {r} -> (invert (invert r)) == r
  iir==r {r} = trans3 iir==r*ir*iir r*ir*iir==r*id r*id==r
    where iir==r*ir*iir :
            (invert (invert r)) == (r * ((invert r) * (invert (invert r))))
          iir==r*ir*iir = trans3 r==id*r (cong id==r*ir refl) assoc
          -- assoc {r} {ir} {iir} : (r * ir) * iir == r * (ir * iir)
          -- id==r*ir             : id == r * ir
          -- cong % (refl {iir})  : id * iir == (r * ir) * iir 
          -- id*r==r {iir}        : iir == id * iir 
          -- trans3 % %% %%%%     : iir == r * (ir * iir)
          r*ir*iir==r*id : (r * ((invert r) * (invert (invert r)))) == (r * id)
          r*ir*iir==r*id = cong refl r*ir==id

  -- Uniqueness of (left and right) inverse.
  irleftunique : ∀ {r} -> ∀ {s} -> (s * r) == id -> s == (invert r)
  irleftunique {r} {s} s*r==id = trans (symm s*r*ir==s) (s*r*ir==ir)
    where s*r*ir==ir : ((s * r) * (invert r)) == (invert r)
          s*r*ir==ir = trans (cong s*r==id refl) id*r==r
          s*r*ir==s : ((s * r) * (invert r)) == s
          s*r*ir==s = trans3 assoc (cong refl r*ir==id) r*id==r
  irrightunique : ∀ {r} -> ∀ {s} -> (r * s) == id -> s == (invert r)
  irrightunique {r} {s} r*s==id = trans (symm ir*r*s==s) (ir*r*s==ir)
    where ir*r*s==ir : ((invert r) * (r * s)) == (invert r)
          ir*r*s==ir = trans (cong refl r*s==id) r*id==r
          ir*r*s==s : ((invert r) * (r * s)) == s
          ir*r*s==s = trans3 (symm assoc) (cong ir*r==id refl) id*r==r
