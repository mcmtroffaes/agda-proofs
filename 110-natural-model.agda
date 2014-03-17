module 110-natural-model where

open import 010-false-true
open import 020-equivalence
open import 100-natural

-- We prove that there is a model of the naturals within Agda's lambda
-- calculus. This also shows that the Peano axioms are consistent.

data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ

thm-ℕ-is-natural : Natural zero suc _≡_
thm-ℕ-is-natural = record {
  equiv = thm-≡-is-equivalence;
  sucn!=zero = sucn!=zero;
  sucinjective = sucinjective;
  cong = cong;
  induction = induction
  }
  where
    sucn!=zero : ∀ {r} -> suc r ≡ zero -> False
    sucn!=zero ()
    sucinjective : ∀ {r s} -> suc r ≡ suc s -> r ≡ s
    sucinjective refl = refl
    cong : ∀ {r s} -> r ≡ s -> suc r ≡ suc s
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
