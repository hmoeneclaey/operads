{-# OPTIONS --allow-unsolved-metas #-}

module LabelledTree where

open import Data
open import FiniteSet
open import FibrantUniverse
--open import FiniteSet3


data Ltree+ : ℕ → Set where
  ∅+ : Ltree+ (s O)
  cons+ : {n : ℕ} → {S : Fin n → ℕ} → I → ((k : Fin n) → Ltree+ (S k)) → Ltree+ (finiteSum S)
 
data Ltree : ℕ → Set where
  ∅ : Ltree (s O)
  cons : {n : ℕ} → {S : Fin n → ℕ} → ((k : Fin n) → Ltree+ (S k)) → Ltree (finiteSum S)



idLtree : Ltree (s O)
idLtree = ∅

γLtree : {m n : ℕ} → Ltree m → Fin m → Ltree n → Ltree (pred (m + n))
γLtree = {!!}


{-
data Arity+ : {n : ℕ} → LTree+ n → Set where
  ar∅+ : Arity+ ∅+
  arCons+ : {n : ℕ} → {S : Fin n → ℕ} → {i : I} → {T : (k : Fin n) → LTree+ (S k)} → {k : Fin n} → Arity+ (T k) → Arity+ (cons+ i T)

data Arity : {n : ℕ} → LTree n → Set where
  ar∅ : Arity ∅
  arCons : {n : ℕ} → {S : Fin n → ℕ} → {T : (k : Fin n) → LTree+ (S k)} → {k : Fin n} → Arity+ (T k) → Arity (cons T)



instance
  FOArity+ : {n : ℕ} {t : LTree+ n} → FOSet (Arity+ t)
  FOArity+ = {!!}

  FOArity : {n : ℕ} {t : LTree n} → FOSet (Arity t)
  FOArity = {!!}

addLbl : {n : ℕ} → I → LTree n → LTree+ n
addLbl = {!!}

graft+ : {m n : ℕ} → (t₁ : LTree+ (s m)) → (a : Arity+ t₁) → LTree+ n → LTree+ (m + n)
graft+ = {!!}

graft : {m n : ℕ} → (t₁ : LTree (s m)) → (a : Arity t₁) → LTree+ n → LTree+ (m + n)
graft = {!!}
-}
