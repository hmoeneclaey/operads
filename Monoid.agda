{-# OPTIONS --rewriting #-}


--WRONG !!!!


module Monoid where

open import Data
open import Interval


postulate _↦_ : ∀ {k} {A : Set k} → A → A → Set k
{-# BUILTIN REWRITE _↦_ #-}



postulate
  Tree : Set
  • : Tree
  ∅ : Tree
  cons : Tree → I → Tree → I → Tree

  •RightTree : {t₁ : Tree} {i : I} → cons t₁ i • e₀ ≡ t₁
  •LeftTree : {t₂ : Tree} {j : I} → cons • e₀ t₂ j ≡ t₂
  assocTree : {t₁ t₂ t₃ : Tree} {i₁ i₂ i₃ : I} → cons t₁ i₁ (cons t₂ i₂ t₃ i₃) e₀ ≡ cons (cons t₁ i₁ t₂ i₂) e₀ t₃ i₃
--  ∅LeftTree : {t₂ : Tree} {i j : I} → cons ∅ i t₂ j ≡ cons ∅ e₁ t₂ j
--  ∅RightTree : {t₁ : Tree} {i j : I} → cons t₁ i ∅ j ≡ cons t₁ i ∅ e₁



module _ {k} {P : Tree → Set k}
        (e• : P •)
        (e∅ : P ∅)
        (econs : {t₁ : Tree} → P t₁ → (i₁ : I) → {t₂ : Tree} → P t₂ → (i₂ : I) → P (cons t₁ i₁ t₂ i₂))
        (_ : (t₁ : Tree) (et₁ : P t₁) (i : I) → transport P •RightTree (econs et₁ i e• e₀) ≡ et₁)
        (_ : (t₂ : Tree) (et₂ : P t₂) (j : I) → transport P •LeftTree (econs e• e₀ et₂ j) ≡ et₂)  
        (_ : (t₁ t₂ t₃ : Tree) (et₁ : P t₁) (et₂ : P t₂) (et₃ : P t₃) (i₁ i₂ i₃ : I) 
                    → transport P assocTree (econs et₁ i₁ (econs et₂ i₂ et₃ i₃) e₀) ≡ econs (econs et₁ i₁ et₂ i₂) e₀ et₃ i₃)
--        (_ : (t₂ : Tree) (et₂ : P t₂) (i j : I) → transport P ∅LeftTree (econs e∅ i et₂ j) ≡ econs e∅ e₁ et₂ j)
--        (_ : (t₁ : Tree) (et₁ : P t₁) (i j : I) → transport P ∅RightTree (econs et₁ i e∅ j) ≡ econs et₁ i e∅ e₁)
       where
           postulate
             TreeElim : (t : Tree) → P t
             TreeElim• : TreeElim • ↦ e•
             {-# REWRITE TreeElim• #-}
             TreeElim∅ : TreeElim ∅ ↦ e∅
             {-# REWRITE TreeElim∅ #-}
             TreeElimCons : (t₁ : Tree) (i₁ : I) (t₂ : Tree) (i₂ : I) → TreeElim (cons t₁ i₁ t₂ i₂) ↦ econs (TreeElim t₁) i₁ (TreeElim t₂) i₂
             {-# REWRITE TreeElimCons #-}




TreeRec : ∀ {k} {H : Set k}
        (e• : H)
        (e∅ : H)
        (econs : H → (i₁ : I) → H → (i₂ : I) → H)
        (_ : (et₁ : H) {i : I} → econs et₁ i e• e₀ ≡ et₁ )
        (_ : (et₂ : H) {j : I} → econs e• e₀ et₂ j ≡ et₂ )
        (_ : (et₁ et₂ et₃ : H) {i₁ i₂ i₃ : I}
                    → econs et₁ i₁ (econs et₂ i₂ et₃ i₃) e₀ ≡ econs (econs et₁ i₁ et₂ i₂) e₀ et₃ i₃ )
 --       (_ : (et₂ : H) {i j : I} → econs e∅ i et₂ j ≡ econs e∅ e₁ et₂ j)
 --       (_ : (et₁ : H) {i j : I} → econs et₁ i e∅ j ≡ econs et₁ i e∅ e₁)
        → Tree → H 
TreeRec = {!!}


arity : Tree → ℕ
arity = TreeRec O (s O) (λ n₁ _ n₂ _ → n₁ + n₂) 
                (λ _ → {!!}) (λ _ → refl) (λ n₁ n₂ n₃  → {!!}) 
                --(λ _ → refl) (λ _ → refl)

