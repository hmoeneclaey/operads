module FiniteSet where

--Module containing basic definitions
open import Data




--We define canonical finite sets, together with their total order


--Intuitively fzero is 0, and fsucc n t is the successor of t.

data Fin : ℕ → Set where
  fzero : (n : ℕ) → Fin (s n)
  fsucc : (n : ℕ) → Fin n → Fin (s n)

--test that Fin O is empty
--FinOempty : Fin O → ⊥
--FinOempty ()

_<_ : {n : ℕ} → Fin n → Fin n → Set
t < fzero n = ⊥
fzero n < fsucc n t = ⊤
fsucc n t₁ < fsucc n t₂ = t₁ < t₂





--We define (small) finite totally ordered sets as instance classes

record FOSet (A : Set) : Set where
  field
    cardinal : ℕ
    isFinite : Fin cardinal ≅ A  

open FOSet {{...}} public


--Defining canonical FOSet
instance 
  canonicalFOSet : {n : ℕ} → FOSet (Fin n)
  canonicalFOSet {n} = record { cardinal = n ; isFinite = isoRefl }


--We show that finite sets are stable by Σ


--Some arithmetic with canonical finite sets

--Stabilitiy by Sigma
