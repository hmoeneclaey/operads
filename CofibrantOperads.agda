module CofibrantOperads where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad
open import FibrantUniverses





module _ {k} {P₁ P₂ : (A : Set) → {{_ : FOSet A}} → Set k} (α : Nat P₁ P₂) where

  FibrationOp : Set (lsuc lzero ⊔ k)
  FibrationOp = (A : Set) → {{_ : FOSet A}} → Fibration (α A)

  ContrMapOp : Set (lsuc lzero ⊔ k)
  ContrMapOp = (A : Set) → {{_ : FOSet A}} → ContrMap (α A)

  record TrivialFibrationOp :  Set (lsuc lzero ⊔ k) where
    field
      isFibOp : FibrationOp
      isContrOp : ContrMapOp



--It is not good that we ask for lifting only in one universe

module _ {k} (P : (A : Set) → {{_ : FOSet A}} → Set k) {{_ : Operad P}} where

  FibOp : Set (lsuc lzero ⊔ k)
  FibOp = (A : Set) → {{_ : FOSet A}} → Fib (P A)

  record lifting {R₁ R₂ : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad R₁}} {{_ : Operad R₂}}
                 (α : Nat R₂ R₁) (β : Nat P R₁) : Set (lsuc lzero ⊔ k) where
         field
           δ : Nat P R₂
           homδ : HomOperad δ
           equal : {A : Set} → {{_ : FOSet A}} → (c : P A) → α A (δ A c) ≡ β A c

  CofibrantOp : Set (lsuc k)
  CofibrantOp = {R₁ R₂ : (A : Set) → {{_ : FOSet A}} → Set k} → {{_ : Operad R₁}} → {{_ : Operad R₂}}
                → (α : Nat R₂ R₁) → HomOperad α → TrivialFibrationOp α
                → (β : Nat P R₁) → HomOperad β
                → lifting α β




