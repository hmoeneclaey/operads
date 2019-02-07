{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

module NfAltOperad where



open import Data
open import FiniteSet



postulate
  +rightS : {m n : ℕ} → m + (s n) ↦ s (m + n)
  {-# REWRITE +rightS #-}
  +rightO : {m : ℕ} → m + O ↦ m
  {-# REWRITE +rightO #-}



ψ : {m n : ℕ} → Fin (s m) → Fin (s n) → Fin (s (m + n))
ψ = {!!}


record NfAltOperad {k} (P : ℕ → Set k) : Set k where

  field
  
    id : P (s O)
    
    γ : {m n : ℕ} (k : Fin (s m)) → P (s m) → P n → P (m + n)
    
    UnitLeft : {n : ℕ} (t : P n)
               → γ fzero id t ≡ t
               
    UnitRight : {m : ℕ} (k : Fin (s m)) (t : P (s m))
                → γ k t id ≡ t

    Assoc₁ : {m n l : ℕ} (k₁ : Fin (s m))(k₂ : Fin (s n))
            (t₁ : P (s m)) (t₂ : P (s n)) (t₃ : P l)
            → (γ k₁ t₁ (γ k₂ t₂ t₃)) ≡ transport P (+Assoc {m} {n} {l}) (γ (ψ k₁ k₂) (γ k₁ t₁ t₂) t₃)
    
    Assoc₂ : {m n l : ℕ} (k₁ : Fin (s (s m))) (k₂ : Fin (s m)) → ⊥



open NfAltOperad {{...}} public


