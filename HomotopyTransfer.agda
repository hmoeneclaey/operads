module HomotopyTransfer where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad



--First we define the endomorphism operad of a morphism

module _ {k} {X Y : Set k} (p : X → Y) where

  record EndMor (A : Set) {{_ : FOSet A}} : Set k where
    constructor _,_,_ 
    field
      π₁ : End X A
      π₂ : End Y A
      equal : (d : A → X) → p (π₁ d) ≡ π₂ (p o d) 


 

  mkEndMor : {A : Set} {{_ : FOSet A}}
               (c₁ : End X A) → (c₂ : End Y A) → ((d : A → X) → p (c₁ d) ≡ c₂ (p o d)) → EndMor A
  mkEndMor c₁ c₂ eq = (c₁ , c₂ , eq)

  ≡EndMor : {A : Set} {{_ : FOSet A}} → {x y : EndMor A}
              → EndMor.π₁ x ≡ EndMor.π₁ y → EndMor.π₂ x ≡ EndMor.π₂ y → x ≡ y
  ≡EndMor {x = ( π₁ , π₂ , _ )}
          {( _ , _ , _ )} refl refl = ap (mkEndMor π₁ π₂) (funext (λ a → UIP))
    



  EndMorFun : arrowAction EndMor
  EndMorFun f {{homf}} (c₁ , c₂ , eq)
            = functor f {{homf}} c₁ ,
              functor f {{homf}} c₂ ,
              λ d → eq (d o f) 
{-
  instance
    CollEndMor : Collection EndMor
    CollEndMor = record { functor = EndMorFun ;
                          functorId = λ _ → refl ;
                          functorComp = λ _ → refl }
-}


  instance
    OpEndMor : Operad EndMor
    OpEndMor = record
                 { functor = EndMorFun
                 ; functorId = λ _ → refl
                 ; functorComp = λ _ → refl
                 ; id = (id , id , λ _ → refl)
                 ; γ = λ c d → (γ (EndMor.π₁ c) (EndMor.π₁ o d) ,
                                γ (EndMor.π₂ c) (EndMor.π₂ o d) ,
                                λ e → ≡Trans (EndMor.equal c _)
                                             (ap (EndMor.π₂ c) (funext (λ a → EndMor.equal (d a) _))) )
                 ; unitLeft = λ _ → ≡EndMor refl refl
                 ; unitRight = λ _ → ≡EndMor refl refl
                 ; naturalityFiber = λ _ _ _ → ≡EndMor refl refl
                 ; naturalityBase = λ _ _ _ → ≡EndMor refl refl
                 ; assoc = λ _ _ _ → ≡EndMor refl refl
                 }


  operadProj₁ : Nat EndMor (End X)
  operadProj₁ A (π₁ , _ , _) = π₁

  HomOpProj₁ : HomOperad operadProj₁ 
  HomOpProj₁ = record { HomCollection = λ _ _ → refl ;
                        HomOperadId = refl ;
                        HomOperadγ = λ _ _ → refl }

  
  operadProj₂ : Nat EndMor (End Y)
  operadProj₂ A (_ , π₂ , _) = π₂

  HomOpProj₂ : HomOperad operadProj₂ 
  HomOpProj₂ = record { HomCollection = λ _ _ → refl ;
                        HomOperadId = refl ;
                        HomOperadγ = λ _ _ → refl }





--Now we show that our situation is good when p is a trivial fibration and X and Y are fibrant

  open import Interval

  module _ {{_ : Fib X}} {{_ : Fib Y}} where
  

    
