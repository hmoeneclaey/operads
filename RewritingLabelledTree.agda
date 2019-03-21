{-# OPTIONS --allow-unsolved-metas #-}

module RewritingLabelledTree where

open import Data
open import LabelledTree

_⇒_ : {n : ℕ} → Ltree n → Ltree n → Set
t ⇒ t' = {!!}

{-
Confluent⇒ : {n : ℕ} {t₁ t₂ t₃ : LTree n} → t₁ ⇒ t₂ → t₁ ⇒ t₃ → LTree n
Confluent⇒ = {!!}
-}
