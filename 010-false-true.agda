module 010-false-true where

-- In Agda, types are theorems, and instances of types are proofs. The
-- simplest theorem is the theorem which has no proof, and is useful
-- to represent any contradictory situation. We declare False as an
-- algebraic data type without constructors. If "False" has no
-- constructors, then it also has no instances, and thereby perfectly
-- serves our purpose.  Note that what we call here "False" is also
-- sometimes also called bottom and is denoted by ⊥.

data False : Set where

-- The next simplest theorem is the trivial theorem which is always
-- true. We declare it as an algebraic data type "True", with one
-- constructor named "trivial".

data True : Set where
  trivial : True
