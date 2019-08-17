{-# OPTIONS --allow-unsolved-metas #-}

module LabelledTree where

open import Data
open import FiniteSet
open import FibrantUniverse



--Main definition

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




--We show some tools to manipulate Ltree

≡cons+ : {n : ℕ} {S : Fin n → ℕ} {i₁ i₂ : I} {t₁ t₂ : (k : Fin n) → Ltree+ (S k)}
         → i₁ ≡ i₂ → ((k : Fin n) → t₁ k ≡ t₂ k)
         → cons+ i₁ t₁ ≡ cons+ i₂ t₂
≡cons+ {i₁ = i₁} refl hyp = ap (λ t → cons+ i₁ t) (funext hyp)

≡cons : {n : ℕ} {S : Fin n → ℕ} {t₁ t₂ : (k : Fin n) → Ltree+ (S k)}
         → ((k : Fin n) → t₁ k ≡ t₂ k)
         → cons t₁ ≡ cons t₂
≡cons hyp = ap cons (funext hyp)



--We define i ∩ t for i : I and t a labelled tree

_∩tree+_ : {n : ℕ} → I → Ltree+ n → Ltree+ n
i ∩tree+ ∅+ = ∅+
i ∩tree+ cons+ j t = cons+ (i ∩ j) (λ k → i ∩tree+ (t k))

infix 35 _∩tree+_

_∩tree_ : {n : ℕ} → I → Ltree n → Ltree n
i ∩tree ∅ = ∅
i ∩tree cons t = cons λ k → i ∩tree+ (t k)

infix 37 _∩tree_

≡∩tree+₁ : {n : ℕ} {t : Ltree+ n} → e₁ ∩tree+ t ≡ t 
≡∩tree+₁ {t = ∅+} = refl
≡∩tree+₁ {t = cons+ j t} = ≡cons+ ∩left₁ λ k → ≡∩tree+₁

≡∩tree₁ : {n : ℕ} {t : Ltree n} → e₁ ∩tree t ≡ t
≡∩tree₁ {t = ∅} = refl
≡∩tree₁ {t = cons x} = ≡cons (λ k → ≡∩tree+₁)

μ : {n : ℕ} → Ltree n
μ {n} = transport Ltree ≡Sum1 (cons {n} λ _ → ∅+)




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
