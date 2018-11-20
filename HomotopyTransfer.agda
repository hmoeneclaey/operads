module HomotopyTransfer where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad


module _ {k} {X Y : Set k} (p : X → Y) where

  record EndMor (A : Set) {{_ : FOSet A}} : Set k where
    field
      π₁ : End X A
      π₂ : End Y A
      equal : (d : A → X) → p (π₁ d) ≡ π₂ (p o d) 


 

  mkEndMor : {A : Set} {{_ : FOSet A}}
               (c₁ : End X A) → (c₂ : End Y A) → ((d : A → X) → p (c₁ d) ≡ c₂ (p o d)) → EndMor A
  mkEndMor c₁ c₂ eq = record { π₁ = c₁ ; π₂ = c₂ ; equal = eq }

  ≡EndMor : {A : Set} {{_ : FOSet A}} → {x y : EndMor A}
              → EndMor.π₁ x ≡ EndMor.π₁ y → EndMor.π₂ x ≡ EndMor.π₂ y → x ≡ y
  ≡EndMor {x = record { π₁ = π₁ ; π₂ = π₂ ; equal = equal }}
          {record { π₁ = π₁' ; π₂ = π₂' ; equal = equal' }} refl refl = ap (mkEndMor π₁ π₂) (funext (λ a → UIP))
    



  EndMorFun : arrowAction EndMor
  EndMorFun f {{homf}} record { π₁ = c₁ ; π₂ = c₂ ; equal = eq }
            = record { π₁ = EndFun X f {{homf}} c₁ ;
                       π₂ = EndFun Y f {{homf}} c₂ ;
                       equal = λ d → eq (d o f) }

  instance
    CollEndMor : Collection EndMor
    CollEndMor = record { functor = EndMorFun ;
                          functorId = λ _ → refl ;
                          functorComp = λ _ → refl }

  instance
    OpEndMor : Operad EndMor
    OpEndMor = record
                 { id = record { π₁ = λ c → c fzero ;
                                 π₂ = λ c → c fzero ;
                                 equal = λ _ → refl }
                 ; γ = λ c d → record { π₁ = λ f → (EndMor.π₁ c) (λ a → EndMor.π₁ (d a) (λ b → f (a , b))) ;
                                        π₂ = λ f → (EndMor.π₂ c) (λ a → EndMor.π₂ (d a) (λ b → f (a , b))) ;
                                        equal = λ d → {!!} }
                 ; unitLeft = λ _ → ≡EndMor refl refl
                 ; unitRight = λ _ → ≡EndMor refl refl
                 ; naturalityFiber = λ _ _ _ → ≡EndMor refl refl
                 ; naturalityBase = λ _ _ _ → ≡EndMor refl refl
                 ; assoc = λ _ _ _ → ≡EndMor refl refl
                 }


