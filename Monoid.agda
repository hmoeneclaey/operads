{-# OPTIONS --rewriting #-}

module Monoid where


open import Data
open import FiniteSet
open import MorphismFiniteSet
open import Operad
open import FibrantUniverse
open import LabelledTree
open import QuotientLabelledTree




--We define ∞Mon

record ∞Mon (A : Set) {{_ : FOSet A}} : Set where
  constructor _::_::_
  field
    tree : Qtree
    ∞arity : Fin (Arity tree) → A
    ∞hom : HomFO ∞arity



--Preliminary results about ∞Mon

∞Mon≡Aux : {A : Set} {{_ : FOSet A}} {t : Qtree}
           {f₁ f₂ : Fin (Arity t) → A} {homf₁ : HomFO f₁} {homf₂ : HomFO f₂}
           → f₁ ≡ f₂ → (t :: f₁ :: homf₁) ≡ (t :: f₂ :: homf₂)

∞Mon≡Aux {t = t} {f₁ = f₁} refl = ap (λ x → t :: f₁ :: x) PropHomFO


∞Mon≡ : {A : Set} {{_ : FOSet A}} → {x₁ x₂ : ∞Mon A}
        → ∞Mon.tree x₁ ≡ ∞Mon.tree x₂ → x₁ ≡ x₂

∞Mon≡ {x₁ = t₁ :: f₁ :: homf₁} {t₂ :: f₂ :: homf₂} refl = ∞Mon≡Aux (HomFOUnique homf₁ homf₂)




--We show that ∞Mon is an operad

instance
  ∞MonOp : Operad ∞Mon
  ∞MonOp = record
             { functor = λ { f homf (t :: g :: homg)
                                  → (t :: f o g :: HomFOComp homg homf) }
                                  
             ; functorId = λ { (t :: f :: homf) → ∞Mon≡ refl}
             
             ; functorComp = λ { (t :: f :: homf) → ∞Mon≡ refl}
             
             ; id = [ ∅ ] :: Id :: HomFOId
             
             ; γ = {!!}
             
             ; unitLeft = {!!}
             
             ; unitRight = {!!}
             
             ; naturalityFiber = {!!}
             
             ; naturalityBase = {!!}
             
             ; assoc = {!!}
             }
