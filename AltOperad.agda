{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

module AltOperad where

open import Agda.Primitive
open import Data
open import FiniteSet



--We add some rewriting

postulate
  OLeftRewrite : (n : ℕ) → n + O ↦ n
  {-# REWRITE OLeftRewrite #-}
  sLeftRewrite : (m n : ℕ) → m + (s n) ↦ s (m + n)
  {-# REWRITE sLeftRewrite #-}
  


--Some Auxiliary equalities and definitions

≡AssocAlt₁ : (m n l : ℕ) → pred (m + n + l) ≡ pred (m + (n + l))
≡AssocAlt₁ m n l = ap pred (+Assoc {m} {n} {l})

≡AssocAlt₂ : (m n l : ℕ) → pred (m + l + n) ≡ pred (m + n + l)
≡AssocAlt₂ m n l = ≡Trans (≡AssocAlt₁ m l n)
                          (≡Trans (ap (λ y → pred (m + y)) {x = l + n} {y = n + l} (+Com {n} {l}))
                                  (≡Sym (≡AssocAlt₁ m n l))) 

assocAltFin₁ : {m n : ℕ} → Fin m → Fin (s n) → Fin (m + n)
assocAltFin₁ = {!!}

assocAltFin₂ : {m : ℕ} (n : ℕ) (k₁ k₂ : Fin (s m)) → k₁ << k₂ → Fin (m + n)
assocAltFin₂ = {!!}

assocAltFin₃ : {m : ℕ} (l : ℕ) (k₁ k₂ : Fin (s m)) → k₁ << k₂ → Fin (m + l)
assocAltFin₃ = {!!}



--Alternative definition of operads

record AltOperad {k} (P : ℕ → Set k) : Set k where
  field

    idAlt : P (s O)

    γAlt : {m n : ℕ} → P m → Fin m → P n → P (pred (m + n))

    unitAlt₁ : {m : ℕ} (c : P m) → γAlt idAlt fzero c ≡ c

    unitAlt₂ :  {m : ℕ} (c : P m) {k : Fin m} → γAlt c k idAlt ≡ c

    assocAlt₁ : {m n l : ℕ} (c : P m) (d : P (s n)) (e : P l) {k₁ : Fin m} {k₂ : Fin (s n)}
               → γAlt c k₁ (γAlt d k₂ e) ≡ transport P (≡AssocAlt₁ m n l) (γAlt (γAlt c k₁ d) (assocAltFin₁ k₁ k₂) e)

    assocAlt₂ : {m n l : ℕ} (c : P (s m)) (d : P n) (e : P l) {k₁ k₂ : Fin (s m)} (eq : k₁ << k₂)
                → (γAlt (γAlt c k₁ d) (assocAltFin₂ n k₁ k₂ eq) e)
                ≡ transport P (≡AssocAlt₂ m n l) (γAlt (γAlt c k₂ e) (assocAltFin₃ l k₁ k₂ eq) d)

open AltOperad {{...}} public



--We define morphism of alternative operads


record HomAltOperad {k l} {P : ℕ → Set k} {{_ : AltOperad P}}
                          {Q : ℕ → Set l} {{_ : AltOperad Q}}
                          (α : {n : ℕ} → P n → Q n) : Set (k ⊔ l) where
       field
       
         HomIdAlt : α idAlt ≡ idAlt
         
         HomγAlt : {m n : ℕ} (c : P m) {k : Fin m} (d : P n) → α (γAlt c k d) ≡ γAlt (α c) k (α d)  
