module 040-monoid where

-- We need semigroups.

open import 030-semigroup

-- The next useful structure is a monoid, which is a semigroup with
-- (left and right) identity element.

record Monoid
  {M : Set}
  (_==_ : M -> M -> Set)
  (_*_ : M -> M -> M)
  (id : M)
  : Set1 where

  field
    semigroup : SemiGroup _==_ _*_
    r*id==r : ∀ {r} -> (r * id) == r
    id*r==r : ∀ {r} -> (id * r) == r

  open SemiGroup semigroup public

  -- Should we define powers? We cannot do this yet: we need natural
  -- numbers first, which we do not have yet.

  -- Let us prove some facts.

  -- Identity can occur on either side of the equality.
  r==r*id : ∀ {r} -> r == (r * id)
  r==r*id = symm r*id==r
  r==id*r : ∀ {r} -> r == (id * r)
  r==id*r = symm id*r==r

  -- The identity element is unique (both left and right).
  idleftunique : ∀ {r} -> (∀ {s} -> (r * s) == s) -> (r == id)
  idleftunique r*s==s = trans r==r*id r*s==s

  idrightunique : ∀ {r} -> (∀ {s} -> (s * r) == s) -> (r == id)
  idrightunique s*r==s = trans r==id*r s*r==s
