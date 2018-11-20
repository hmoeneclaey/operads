--{-# OPTIONS --rewriting #-}


module Monoid where

open import Data
open import Interval


{-
postulate _↦_ : ∀ {k} {A : Set k} → A → A → Set k
{-# BUILTIN REWRITE _↦_ #-}
-}



postulate
  Tree : Set
  • : Tree
  cons∅∅ : Tree
  cons∅* : I → Tree → Tree
  cons*∅ : I → Tree → Tree
  cons** : I → Tree → I → Tree → Tree

--Now tons of equalities

--Eight cases for associativity  
  assocTree1 : cons∅* e₀ cons∅∅ ≡ cons*∅ e₀ cons∅∅
  assocTree2 : {t₃ : Tree} {i₃ : I} → cons∅* e₀ (cons∅* i₃ t₃) ≡ cons** e₀ (cons∅∅) i₃ t₃
  assocTree3 : {t₂ : Tree} {i₂ : I} → cons∅* e₀ (cons*∅ i₂ t₂) ≡ cons*∅ e₀ (cons∅* i₂ t₂)
  assocTree4 : {t₂ t₃ : Tree} {i₂ i₃ : I} → cons∅* e₀ (cons** i₂ t₂ i₃ t₃) ≡ cons** e₀ (cons∅* i₂ t₂) i₃ t₃
  assocTree5 : {t₁ : Tree} {i₁ : I} → cons** i₁ t₁ e₁ cons∅∅ ≡ cons*∅ e₀ (cons*∅ i₁ t₁)
  assocTree6 : {t₁ t₂ : Tree} {i₁ i₂ : I} → cons** i₁ t₁ e₀ (cons*∅ i₂ t₂) ≡ cons*∅ e₀ (cons** i₁ t₁ i₂ t₂)
  assocTree7 : {t₁ t₃ : Tree} {i₁ i₃ : I} → cons** i₁ t₁ e₀ (cons∅* i₃ t₃) ≡ cons** e₀ (cons*∅ i₁ t₁) i₃ t₃
  assocTree8 : {t₁ t₂ t₃ : Tree} {i₁ i₂ i₃ : I} → cons** i₁ t₁ e₀ (cons** i₂ t₂ i₃ t₃) ≡ cons** e₀ (cons** i₁ t₁ i₂ t₂) i₃ t₃

--Note that cons∅* e₀ • will be the identity
  unitTree1 : cons*∅ e₀ • ≡ cons∅* e₀ •
  unitTree2 : {t : Tree} {i : I} → cons** e₀ • i t ≡ cons** i t e₀ •

--We eliminate identity in the middle of the tree
  idMidTree1 : {t₁ : Tree} {i i₁ : I} → cons*∅ i (cons** i₁ t₁ e₀ •) ≡ cons*∅ (i ⊔ i₁) t₁
  idMidTree2 : {t₁ t₃ : Tree} {i i₁ i₃ : I} → cons** i (cons** i₁ t₁ e₀ •) i₃ t₃ ≡ cons** (i ⊔ i₁) t₁ i₃ t₃
  idMidTree3 : {t₂ : Tree} {i i₂ : I} → cons∅* i (cons** i₂ t₂ e₀ •) ≡ cons∅* (i ⊔ i₂) t₂
  idMidTree4 : {t₁ t₂ : Tree} {i i₁ i₂ : I} → cons** i₁ t₁ i (cons** i₂ t₂ e₀ •) ≡ cons** i₁ t₁ (i ⊔ i₂) t₂

--We eliminate idenity at the top of the tree
  idTopTree1 : {i : I} → cons∅* i (cons∅* e₀ •) ≡ cons∅∅
  idTopTree2 : {i : I} → cons*∅ i (cons∅* e₀ •) ≡ cons∅∅
  idTopTree3 : {t₂ : Tree} {i i₂ : I} → cons** i (cons∅* e₀ •) i₂ t₂ ≡ cons∅* i₂ t₂
  idTopTree4 : {t₁ : Tree} {i i₁ : I} → cons** i₁ t₁ i (cons∅* e₀ •) ≡ cons*∅ i₁ t₁

--We note that the elimination of identity at the bottom cannot be done in the style of a HIT



--We postulate the elimination principle

module _ {k} {P : Tree → Set k}
         (e• : P •)
         (econs∅∅ : P cons∅∅)
         (econs∅* : (i : I) → {t : Tree} → P t → P (cons∅* i t)) 
         (econs*∅ : (i : I) → {t : Tree} → P t → P (cons*∅ i t))
         (econs** : (i₁ : I) → {t₁ : Tree} → P t₁ → (i₂ : I) → {t₂ : Tree} → P t₂ → P (cons** i₁ t₁ i₂ t₂))
       where
       postulate
         TreeElim : (t : Tree) → P t


