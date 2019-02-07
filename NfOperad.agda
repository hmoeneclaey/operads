{-# OPTIONS --allow-unsolved-metas #-}

module NfOperad where


open import Data
open import FiniteSet




--We define a bit more about finite sets

FinΣ : {n : ℕ} (S : Fin n → ℕ) → Set
FinΣ {n} S = Σ (Fin n) (λ k → Fin (S k))

FinΣIso : {n : ℕ} {S : Fin n → ℕ} → Fin (finiteSum S) → FinΣ S
FinΣIso {S = S} = iso.inv (isIsoCanonicalΣ S)

Nfη₂ : {n : ℕ} → n ≡ finiteSum (λ (_ : Fin n) → s O)
Nfη₂ {O} = refl
Nfη₂ {s n} = ap s Nfη₂

Nfη₁ : (S : Fin(s O) → ℕ) → S fzero ≡ finiteSum S
Nfη₁ S = ≡Sym +O

Nfψ : {n : ℕ} {S : Fin n → ℕ} (Q : FinΣ S → ℕ) → finiteSum (λ k → finiteSum (λ l → Q (k , l))) ≡ finiteSum (Q o FinΣIso)
Nfψ {O} _ = refl
Nfψ {s n} Q = {!!}




--We define non-functorial operads


record NfOperad {k} (P : ℕ → Set k) : Set k where

  field
  
    NfId : P (s O)
    
    Nfγ : {n : ℕ} → {S : Fin n → ℕ} → P n → ((k : Fin n) → P (S k)) → P (finiteSum S)
    
    NfUnitLeft : {n : ℕ} (c : P n) → Nfγ c (λ _ → NfId) ≡ transport P (Nfη₂) c

    NfUnitRight : {S : Fin(s O) → ℕ} (d : (k : Fin(s O)) → P (S k))
                  → Nfγ NfId d ≡ transport P (Nfη₁ S) (d fzero)

    NfAssoc : {n : ℕ} {S : Fin n → ℕ} {Q : FinΣ S → ℕ} (c : P n) (d : (k : Fin n) → P (S k))
              (e : (x : FinΣ S) → P (Q x))
              → Nfγ (Nfγ c d) (λ k → e (FinΣIso k)) ≡ transport P (Nfψ Q) (Nfγ c (λ k → Nfγ (d k) (λ l → e (k , l))))



open NfOperad {{...}} public
