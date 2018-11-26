module CofibrantOperads where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad
open import FibrantUniverses





module _ {k l} {P₁ : (A : Set) → {{_ : FOSet A}} → Set k}
               {P₂ : (A : Set) → {{_ : FOSet A}} → Set l}
               (α : Nat P₁ P₂) where

  FibrationOp : Set (lsuc lzero ⊔ (k ⊔ l))
  FibrationOp = (A : Set) → {{_ : FOSet A}} → Fibration (α A)

  ContrMapOp : Set (lsuc lzero ⊔ (k ⊔ l))
  ContrMapOp = (A : Set) → {{_ : FOSet A}} → ContrMap (α A)

  TrivialFibrationOp :  Set (lsuc lzero ⊔ (k ⊔ l))
  TrivialFibrationOp = (A : Set) → {{_ : FOSet A}} → TrivialFibration (α A)

  mkTrivialFibrationOp : FibrationOp → ContrMapOp → TrivialFibrationOp
  mkTrivialFibrationOp fibp contrp = λ A → record { isFib = fibp A ;
                                                    isContr = contrp A }

  EquivOp : Set (lsuc lzero ⊔ (k ⊔ l))
  EquivOp = (A : Set) → {{_ : FOSet A}} → Equiv (α A)


--It is not good that we ask for lifting only in one universe

module _ {k} (P : (A : Set) → {{_ : FOSet A}} → Set k) {{_ : Operad P}} where

  FibOp : Set (lsuc lzero ⊔ k)
  FibOp = {A : Set} → {{_ : FOSet A}} → Fib (P A)

  module _ {l m} {R₁ : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad R₁}}
                 {R₂ : (A : Set) → {{_ : FOSet A}} → Set m} {{_ : Operad R₂}}
                 (α : Nat R₂ R₁) (β : Nat P R₁) where

         record lifting : Set (lsuc lzero ⊔ (k ⊔ l ⊔ m)) where
           field
             δ : Nat P R₂
             homδ : HomOperad δ
             equal : {A : Set} → {{_ : FOSet A}} → (c : P A) → α A (δ A c) ≡ β A c

         record wkLifting : Set (lsuc lzero ⊔ (k ⊔ l ⊔ m)) where
           field
             δ : Nat P R₂
             homδ : HomOperad δ


CofibrantOp : ∀ {k l m} (P : (A : Set) → {{_ : FOSet A}} → Set m) {{_ : Operad P}} → Set (lsuc k ⊔ (lsuc l ⊔ m)) 
CofibrantOp {k} {l} P = {R₁ : (A : Set) → {{_ : FOSet A}} → Set k} → {{_ : Operad R₁}}
              → {R₂ : (A : Set) → {{_ : FOSet A}} → Set l} → {{_ : Operad R₂}}
                → (α : Nat R₂ R₁) → HomOperad α → TrivialFibrationOp α
                → (β : Nat P R₁) → HomOperad β
                → lifting P α β



--Beware, the universe level are probably not true

postulate
  CofibrantWkLiftingEquivalence : ∀ {k l m} {P : (A : Set) → {{_ : FOSet A}} → Set k} → {{_ : Operad P}} → CofibrantOp {m} {l} P
                                → {R₁ : (A : Set) → {{_ : FOSet A}} → Set l} → {{_ : Operad R₁}} → {{fib₁ : FibOp R₁}}
                                → {R₂ : (A : Set) → {{_ : FOSet A}} → Set m} → {{_ : Operad R₂}} → {{fib₂ : FibOp R₂}}
                                → (α : Nat R₂ R₁) → HomOperad α → EquivOp α
                                → (β : Nat P R₁) → HomOperad β
                                → wkLifting P α β

