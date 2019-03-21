{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

module TreeOperad where

open import Data
open import FiniteSet
open import LabelledTree
open import RewritingLabelledTree
open import AltOperad




instance
  OpLtree : AltOperad Ltree
  OpLtree = record
              { idAlt = idLtree
              ; γAlt = γLtree
              ; unitAlt₁ = {!!}
              ; unitAlt₂ = {!!}
              ; assocAlt₁ = {!!}
              ; assocAlt₂ = {!!}
              }




postulate
  Qtree : ℕ → Set
  [_] : {n : ℕ} → Ltree n → Qtree n
  QtreeQuotient : {n : ℕ} {t₁ t₂ : Ltree n} → t₁ ⇒ t₂ → [ t₁ ] ≡ [ t₂ ]


module _ {k} {n : ℕ} {P : Qtree n → Set k}
         (d : (t : Ltree n) → P [ t ])
         (eq : {t₁ t₂ : Ltree n} (r : t₁ ⇒ t₂) → transport P (QtreeQuotient r) (d t₁) ≡ d t₂ ) where

       postulate
         QtreeElim : (t : Qtree n) → P t
         QtreeCompute : (t : Ltree n) → QtreeElim [ t ] ↦ d t
         {-# REWRITE QtreeCompute #-}


γQtree : {m n : ℕ} → Qtree m → Fin m → Qtree n → Qtree (pred (m + n))
γQtree = ?

instance
  OpQtree : AltOperad Qtree
  OpQtree = {!!}
