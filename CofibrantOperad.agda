module CofibrantOperad where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad
open import FibrantUniverse

--We use the cocylinder factorisation for operads
open import OperadCocylinder


--We define fibrations / trivial fibrations / equivalence between operads


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






--We define lifting properties for morphism of operad

module _ {k} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}} where

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



--We define fibrant and cofibrant operads

module _ {k} (P : (A : Set) → {{_ : FOSet A}} → Set k) {{_ : Operad P}} where

  FibOp : Set (lsuc lzero ⊔ k)
  FibOp = {A : Set} → {{_ : FOSet A}} → Fib (P A)



module _ {k} (P : (A : Set) → {{_ : FOSet A}} → Set k) {{_ : Operad P}} where

  --Note that being cofibrant is not a type (it is in Setω)
  
  CofibrantOp : Setω --∀ {n₁ n₂} → Set (k ⊔ (lsuc n₁ ⊔ lsuc n₂)) 
  CofibrantOp = ∀ {n₁} {n₂} {R₁ : (A : Set) → {{_ : FOSet A}} → Set n₁} → {{_ : Operad R₁}} → {{_ : FibOp R₁}}
                  → {R₂ : (A : Set) → {{_ : FOSet A}} → Set n₂} → {{_ : Operad R₂}}
                  → (α : Nat R₂ R₁) → HomOperad α → TrivialFibrationOp α
                  → (β : Nat P R₁) → HomOperad β
                  → lifting α β




--Now we show that a cofibrant operads has weak lifting for equivalence between fibrant operads


module _ {k l} {P₁ : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P₁}} {{_ : FibOp P₁}}
         {P₂ : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad P₂}} {{_ : FibOp P₂}}
         {α : Nat P₁ P₂} {{homα : HomOperad α}} where

       HomOpSecCyl : HomOperad (secCylOp α)
       HomOpSecCyl = record { homNat = λ _ → refl ;
                              homId = refl ;
                              homγ = refl }

       HomOpProjCyl : HomOperad (projCylOp α)
       HomOpProjCyl = record { homNat = λ _ → refl ;
                               homId = refl ;
                               homγ = refl }

--       TrivFibSecCylOp : TrivialFibrationOp (secCylOp α)
--       TrivFibSecCylOp = λ _ → TrivFibSecCyl

       TrivFibProjCylOp : EquivOp α → TrivialFibrationOp (projCylOp α)
       TrivFibProjCylOp equivα _ = TrivFibProjCyl (equivα _)



module _ {k l m} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}} (cofibP : CofibrantOp P)
                 {R₁ : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad R₁}} {{fib₁ : FibOp R₁}}
                 {R₂ : (A : Set) → {{_ : FOSet A}} → Set m} {{_ : Operad R₂}} {{fib₂ : FibOp R₂}}
                 (α : Nat R₂ R₁) (homα : HomOperad α) (equivα : EquivOp α)
                 (β : Nat P R₁) (homβ : HomOperad β) where


       fillAux : {{_ : HomOperad α}} → lifting (projCylOp α) β
       fillAux = cofibP (projCylOp α) HomOpProjCyl (TrivFibProjCylOp equivα) β homβ


       CofibrantWkLiftingEquivalence : wkLifting α β

       CofibrantWkLiftingEquivalence = let fill = fillAux {{homα}} in

                                       record { δ = secCylOp α ∘ lifting.δ fill ;
                                                homδ = HomOpComp (HomOpSecCyl {{homα = homα}} ) (lifting.homδ fill)  }

