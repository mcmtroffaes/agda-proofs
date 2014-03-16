module 02-equivalence where

-- We have ⊥ (bottom) to represent logical contradiction.

open import 01-bottom public

-- Next, we need to be able to work with equalities. Equalities are
-- defined between objects of the same type. Two objects are equal if
-- we have a proof of their equality. In Agda, we can represent this
-- by means of a function which takes two instances of some type M,
-- and maps this to a proof of equality.

-- To be a reasonable model for equality, we demand that this function
-- has the properties of an equivalence relation: (i) we must have a
-- proof that every object r in M equals itself, (ii) given a proof
-- that r == s, we must be able to prove that s == r, and (iii) given
-- proofs of r == s and s == t, we must be able to prove that r == t.

-- A convenient way to store all these properties, goes by means of a
-- record, which is in essence a local parametrised module, where the
-- parameters and fields correspond to postulates (theorems that can
-- be stated without proof), and declarations are theorems derived
-- from parameters and fields. A good question is, what should be a
-- parameter, and what should be a field? Fields can be considered as
-- named parameters, so probably anything that would otherwise not be
-- obvious without name should go into a field.

-- Here we declare the type and equality function (which maps pairs of
-- elements to proofs) as parameters, and the equivalence axioms as
-- fields. The parameter M is optional because it can be derived
-- unambiguously from the type signature of the equality function.

record Equivalence
  {M : Set}
  (_==_ : M -> M -> Set)
  : Set1 where

  {- axioms -}
  field
    refl : ∀ {r} -> (r == r)
    symm : ∀ {r s} -> (r == s) -> (s == r)
    trans : ∀ {r s t} -> (r == s) -> (s == t) -> (r == t)

  -- We have a proof of inequality if we can prove contradiction from
  -- equality, and this is precisely how we define the inequality
  -- relation.

  _!=_ : M -> M -> Set
  m != n = (m == n) -> ⊥

  -- Prove transitivity chains.
  -- (TODO: Use a type dependent function for these chains.)
  trans3 : ∀ {r s t u}
           -> (r == s) -> (s == t) -> (t == u) -> (r == u)
  trans3 p1 p2 p3 = trans (trans p1 p2) p3
  trans4 : ∀ {r s t u v}
           -> (r == s) -> (s == t) -> (t == u) -> (u == v) -> (r == v)
  trans4 p1 p2 p3 p4 = trans (trans3 p1 p2 p3) p4
  trans5 : ∀ {r s t u v w}
           -> (r == s) -> (s == t) -> (t == u) -> (u == v) -> (v == w)
           -> (r == w)
  trans5 p1 p2 p3 p4 p5 = trans (trans4 p1 p2 p3 p4) p5
  trans6 : ∀ {r s t u v w x}
           -> (r == s) -> (s == t) -> (t == u) -> (u == v) -> (v == w)
           -> (w == x) -> (r == x)
  trans6 p1 p2 p3 p4 p5 p6 = trans (trans5 p1 p2 p3 p4 p5) p6
