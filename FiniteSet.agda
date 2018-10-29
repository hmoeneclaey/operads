module FiniteSet where

--Module containing basic definitions
open import Data




--We define canonical finite sets, together with their total order


--Intuitively fzero is 0, and fsucc n t is the successor of t.

data Fin : ℕ → Set where
  fzero : (n : ℕ) → Fin (s n)
  fsucc : (n : ℕ) → Fin n → Fin (s n)

--NOT USED FOR NOW
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

finiteSum : {n : ℕ} (f : Fin n → ℕ) → ℕ
finiteSum {O} _ = O
finiteSum {s n} f = f (fzero n) + finiteSum (f o fsucc n)

--QUESTION : should I define this
Fin⊥ : Fin O → ⊥
Fin⊥ ()

Fin+ : {m n : ℕ} → Fin (m + n) ≅ Fin m ∨ Fin n
Fin+ {O} = iso∨⊥ Fin⊥
Fin+ {s m} = {!!}

isoCanonicalΣ : {n : ℕ} (f : Fin n → ℕ) → Fin (finiteSum f) ≅ Σ (Fin n) (λ x → Fin (f x))
isoCanonicalΣ {O} _ = iso⊥ Fin⊥ (λ { (a , _) → Fin⊥ a}) 
isoCanonicalΣ {s n} f = {!!}


--Stabilitiy by Sigma
--QUESTION What should I use instead of {{a : A → Bfinite (B a)}} ?
instance 
  finiteΣ : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : (a : A) → FOSet (B a)}} → FOSet (Σ A B)
  finiteΣ {A} ⦃ record { cardinal = |A| ; 
                         isFinite = record { isoFun = f ; isIso = isof } } ⦄ 
          {B} ⦃ Bfinite ⦄ = let S : Fin |A| →  ℕ 
                                S = λ (a : Fin |A|) → cardinal {B (f a)} {{Bfinite (f a)}}  --weird
                            in record { cardinal = finiteSum S ; 
                                        isFinite = isoTrans (Σ (Fin |A|) (B o f)) 
                                            (isoTrans (Σ (Fin |A|) (λ a → Fin (S a))) 
                                                      (isoCanonicalΣ S) (isoΣfibre {B₂ = B o f} (λ a → isFinite {B (f a)} {{Bfinite (f a)}}))) --weird
                                            (isoΣbase f isof) }

