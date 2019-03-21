{-# OPTIONS --allow-unsolved-metas #-}

module RewritingLabelledTree where

open import Data
open import LabelledTree
open import FiniteSet
open import FibrantUniverse


_⇒_ : {n : ℕ} → Ltree n → Ltree n → Set
t ⇒ t' = {!!}

infix 30 _⇒_

data _⇒*_ {n : ℕ} : Ltree n → Ltree n → Set where
  rewriteO : {t : Ltree n} → t ⇒* t
  rewriteS : {t₁ t₂ t₃ : Ltree n} → t₁ ⇒* t₂ → t₂ ⇒ t₃ → t₁ ⇒* t₃

infix 30 _⇒*_


γLtreeLeft⇒ : {m n : ℕ} {t₁ t₂ : Ltree m} {k : Fin m} {t : Ltree n}
              → t₁ ⇒ t₂ → γLtree t₁ k t ⇒ γLtree t₂ k t
γLtreeLeft⇒ = {!!}

γLtreeRight⇒ : {m n : ℕ} {t₁ t₂ : Ltree n} {k : Fin m} {t : Ltree m}
               → t₁ ⇒ t₂ → γLtree t k t₁ ⇒ γLtree t k t₂
γLtreeRight⇒ = {!!}

∩tree⇒ : {n : ℕ} {t₁ t₂ : Ltree n} {i : I} → t₁ ⇒ t₂ → i ∩tree t₁ ⇒ i ∩tree t₂
∩tree⇒ = {!!}

⇒*∩tree₀ : {n : ℕ} {t : Ltree n} → e₀ ∩tree t ⇒* μ
⇒*∩tree₀ = {!!}


{-
Confluent⇒ : {n : ℕ} {t₁ t₂ t₃ : LTree n} → t₁ ⇒ t₂ → t₁ ⇒ t₃ → LTree n
Confluent⇒ = {!!}
-}
