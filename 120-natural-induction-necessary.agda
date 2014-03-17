module 120-natural-induction-necessary where

open import 010-bottom
open import 020-equivalence
open import 100-natural

-- We prove that the induction axiom is necessary.

-- Peano axioms without induction.

record NaturalWithoutInduction
  {M : Set}
  (zero : M)
  (suc : M -> M)
  (_==_ : M -> M -> Set)
  : Set1 where

  -- axioms
  field
    equiv : Equivalence _==_
    sucn!=zero : ∀ {r} -> suc r == zero -> False
    sucinjective : ∀ {r s} -> suc r == suc s -> r == s
    cong : ∀ {r s} -> r == s -> suc r == suc s
    not-induction :
      ((p : M -> Set) -> p zero -> (∀ n -> p n -> p (suc n)) -> ∀ n -> p n)
      -> False

  open Equivalence equiv public

-- Construct a model, and prove it satisfies NaturalWithoutInduction
-- but not Natural. To do this, we add an extra zero.

data M : Set where
  zero1 : M
  zero2 : M
  suc : M -> M

data _==_ : M -> M -> Set where
  refl : ∀ {r} -> r == r

thm-M-==-is-equivalence : Equivalence _==_
thm-M-==-is-equivalence = record {
  refl = refl;
  symm = symm;
  trans = trans
  }
  where
    symm : ∀ {r s} -> r == s -> s == r
    symm refl = refl
    trans : ∀ {r s t} -> r == s -> s == t -> r == t
    trans refl refl = refl

thm-M-is-natural-without-induction : NaturalWithoutInduction zero1 suc _==_
thm-M-is-natural-without-induction = record {
  equiv = thm-M-==-is-equivalence;
  sucn!=zero = sucn!=zero;
  sucinjective = sucinjective;
  cong = cong;
  not-induction = not-induction
  }
  where
    sucn!=zero : ∀ {r} -> suc r == zero1 -> False
    sucn!=zero ()
    sucinjective : ∀ {r s} -> suc r == suc s -> r == s
    sucinjective refl = refl
    cong : ∀ {r s} -> r == s -> suc r == suc s
    cong refl = refl
    -- To prove that induction fails, we test the property "is a
    -- successor of zero1 but not of zero2". This holds for zero1 (the
    -- base case), and it also holds for every successor of n if it
    -- holds for n, but it does not hold for zero2 (or for any of its
    -- successors).
    not-induction :
      ((p : M -> Set) -> p zero1 -> (∀ n -> p n -> p (suc n)) -> ∀ n -> p n)
      -> False
    not-induction induction = induction p base hypothesis zero2
      where
        -- Property "is a successor of zero1 but not a successor of zero2".
        p : M -> Set
        p zero1 = True  -- true for zero1
        p zero2 = False -- false (no proof) for zero2
        p (suc n) = p n -- true for successor of n if and only if true for n

        -- Base case is trivial.
        base : p zero1
        base = trivial

        -- Induction hypothesis follows by application of "p n" itself
        -- due to the recursive definition of p.
        hypothesis : ∀ n -> p n -> p (suc n)
        hypothesis n pn = pn

-- To round this off, we explicitly prove that M is not natural.

thm-M-is-not-natural : (Natural zero1 suc _==_) -> False
thm-M-is-not-natural nat =
  (NaturalWithoutInduction.not-induction thm-M-is-natural-without-induction)
  (Natural.induction nat)
