module 100-naturals where

open import 010-bottom
open import 020-equivalence

record Natural
  {N : Set}
  (zero : N)
  (suc : N -> N)
  (_==_ : N -> N -> Set)
  : Set1 where

  -- axioms
  field
    equiv : Equivalence _==_
    sucn!=zero : ∀ {r} -> suc r == zero -> ⊥
    sucinjective : ∀ {r s} -> suc r == suc s -> r == s
    cong : ∀ {r s} -> r == s -> suc r == suc s
    induction : (p : N -> Set) -> p zero -> (∀ n -> p n -> p (suc n)) -> (∀ n -> p n)

  open Equivalence equiv public

-- We prove that there is a model of the naturals within Agda's lambda
-- calculus.

data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ

data _==_ : ℕ -> ℕ -> Set where
  refl : ∀ {r} -> r == r

thm-ℕ-==-is-equivalence : Equivalence _==_
thm-ℕ-==-is-equivalence = record {
  refl = refl;
  symm = symm;
  trans = trans
  }
  where
    symm : ∀ {r s} -> r == s -> s == r
    symm refl = refl
    trans : ∀ {r s t} -> r == s -> s == t -> r == t
    trans refl refl = refl

thm-ℕ-is-natural : Natural zero suc _==_
thm-ℕ-is-natural = record {
  equiv = thm-ℕ-==-is-equivalence;
  sucn!=zero = sucn!=zero;
  sucinjective = sucinjective;
  cong = cong;
  induction = induction
  }
  where
    sucn!=zero : ∀ {r} -> suc r == zero -> ⊥
    sucn!=zero ()
    sucinjective : ∀ {r s} -> suc r == suc s -> r == s
    sucinjective refl = refl
    cong : ∀ {r s} -> r == s -> suc r == suc s
    cong refl = refl

    -- This is the only tricky bit: proving the principle of induction.
    induction : (p : ℕ -> Set) -> p zero -> (∀ n -> p n -> p (suc n)) -> ∀ n -> p n
    -- We first prove that p n holds for n equal to zero. This is just
    -- the base case.
    induction p base hypothesis zero = base
    -- Then we prove that p (suc n) holds, using induction on n, that is,
    -- we may assume that p n is proven, or more precisely, that
    -- "induction p base hypothesis n" is a proof of p n.
    induction p base hypothesis (suc n) =
      hypothesis n (induction p base hypothesis n)
