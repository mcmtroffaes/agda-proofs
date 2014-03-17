module 100-natural where

open import 010-false-true
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
    sucn!=zero : ∀ {r} -> suc r == zero -> False
    sucinjective : ∀ {r s} -> suc r == suc s -> r == s
    cong : ∀ {r s} -> r == s -> suc r == suc s
    induction : (p : N -> Set) -> p zero -> (∀ n -> p n -> p (suc n)) -> (∀ n -> p n)

  open Equivalence equiv public
