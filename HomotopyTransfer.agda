module HomotopyTransfer where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad
open import FibrantUniverse
open import CofibrantOperad



--In this file we show that algebras for cofibrant operads are invariant by equivalence



{-
  First we define the endomorphism operad of a morphism p : X → Y
  The situation is that we have a diagram of operads

      End X ← EndMor p → End Y

  EndMor p is useful to link End X and End Y
-}


module _ {k} {l} {X : Set k} {Y : Set l} (p : X → Y) where

  record EndMor (A : Set) {{_ : FOSet A}} : Set (k ⊔ l) where
    constructor _,_,_ 
    field
      π₁ : End X A
      π₂ : End Y A
      equal : (d : A → X) → p (π₁ d) ≡ π₂ (p o d) 


  ≡EndMor : {A : Set} {{_ : FOSet A}} → {x y : EndMor A}
              → EndMor.π₁ x ≡ EndMor.π₁ y → EndMor.π₂ x ≡ EndMor.π₂ y → x ≡ y

  ≡EndMor {x = ( π₁ , π₂ , _ )}
          {( _ , _ , _ )} refl refl = ap (λ eq → (π₁ , π₂ , eq)) (funext (λ a → UIP))
    


  EndMorFun : arrowAction EndMor  
  EndMorFun f homf (c₁ , c₂ , eq)
            = functor f homf c₁ ,
              functor f homf c₂ ,
              λ d → eq (d o f) 


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
                 ; naturalityFiber = λ _ _ _ _ → ≡EndMor refl refl
                 ; naturalityBase = λ _ _ _ _ → ≡EndMor refl refl
                 ; assoc = λ _ _ _ → ≡EndMor refl refl
                 }


  operadProj₁ : Nat EndMor (End X)
  operadProj₁ A (π₁ , _ , _) = π₁

  HomOpProj₁ : HomOperad operadProj₁ 
  HomOpProj₁ = record { homNat = λ _ → refl ;
                        homId = refl ;
                        homγ = refl }

  
  operadProj₂ : Nat EndMor (End Y)
  operadProj₂ A (_ , π₂ , _) = π₂

  HomOpProj₂ : HomOperad operadProj₂ 
  HomOpProj₂ = record { homNat = λ _ → refl ;
                        homId = refl ;
                        homγ = refl }





--Now we show that our situation is good when p is a trivial fibration and X and Y are fibrant
{-In this case :
  • All involved operads are fibrant
  • Proj₂ is a trivial fibration
  • Proj₁ is an equivalence
-}


  module _ {{_ : Fib X}} {{_ : Fib Y}} where

    fibreIsoProj₂Aux : (A : Set) → {{_ : FOSet A}} (g : End Y A)
                       → Σ (End X A) (λ f → (x : A → X) → p (f x) ≡ g (p o x)) ≅ fibre (operadProj₂ A) g

    fibreIsoProj₂Aux A g = record { isoFun = λ {(f , eqf) → (f , g , eqf) , refl} ;
                                    isIso = record { inv = λ {((f , g , eq₁) , refl) → (f , λ x → eq₁ x)} ;
                                                     invLeft = λ {((f , g , eq₁) , refl) → refl} ;
                                                     invRight = λ {(f , eqf) → refl} }}


    fibreIsoProj₂ : (A : Set) → {{_ : FOSet A}} (g : End Y A) →
                    ((x : A → X) → fibre p (g (p o x))) ≅ fibre (operadProj₂ A) g

    fibreIsoProj₂ A g = ≅Trans (record { isoFun = λ sec → (fibre.point o sec) , λ x → fibre.equal (sec x) ;
                                         isIso = record { inv = λ {(f , eqf) x → (f x) , (eqf x)} ;
                                                          invLeft = λ {(f , eqf) → refl };
                                                          invRight = λ sec → refl } }) (fibreIsoProj₂Aux A g)


    ContrProj₂ : ContrMap p → ContrMapOp operadProj₂
    
    ContrProj₂ contrp A = ≅Contr (fibreIsoProj₂ A _) (ΠContr (λ x → contrp))


    FibProj₂ : {{_ : Fibration p}} → FibrationOp operadProj₂
    
    FibProj₂ A =  ≅Fib (fibreIsoProj₂ A _)


    TrivialFibProj₂ : TrivialFibration p → TrivialFibrationOp operadProj₂
    
    TrivialFibProj₂ record { isFib = fibp ; isContr = contrp } = mkTrivialFibrationOp _ (FibProj₂ {{fibp}}) (ContrProj₂ contrp) 


    EndMorFib : TrivialFibration p →  {A : Set} → {{_ : FOSet A}} → Fib (EndMor A)
    
    EndMorFib record { isFib = fibp ; isContr = _ } {A} = totalSpaceFib {{FibProj₂ {{fibp}} A}}


    EquivProj₁ : TrivialFibration p → EquivOp operadProj₁
    
    EquivProj₁ tfibp A = EquivTwoThreeRight {{EndMorFib tfibp}} {g = λ f → λ (s : A → X) → p (f s)}
                                            (EquivPostComp (EquivTrivialFib tfibp))
                                            (Equiv≡ext {f = (λ g s → g (p o s)) o (operadProj₂ A)}
                                                       (λ { (π₁ , π₂ , equal) → funext λ s → ≡Sym (equal _)})
                                                       (EquivComp {{EndMorFib tfibp}}
                                                                  (EquivTrivialFib (TrivialFibProj₂ tfibp A))
                                                                  (EquivPreComp (EquivPostComp (EquivTrivialFib tfibp)))))






module _ {k} {P : (A : Set) → {{_ : FOSet A}} → Set k}
         {{_ : Operad P}} (cofibP : CofibrantOp P) where


       module _ {l m} {X : Set l} {{_ : Fib X}} {Y : Set m} {{_ : Fib Y}}
                (p : X → Y) (tfibp : TrivialFibration p) where


       -- A trivial fibration X → Y gives us that Alg P Y ↔ Alg P X


         algebraBackFibration : Algebra P Y → Algebra P X

         algebraBackFibration record { algebraStruct = εY ; isAlg = isAlgY } =
       
                              let fill = cofibP (operadProj₂ _) (HomOpProj₂ _) (TrivialFibProj₂ _ tfibp) εY isAlgY in

                              record { algebraStruct = operadProj₁ _ ∘ lifting.δ fill ;
                                       isAlg = HomOpComp (HomOpProj₁ _) (lifting.homδ fill) }


         algebraForwardFibration : Algebra P X → Algebra P Y

         algebraForwardFibration record { algebraStruct = εX ; isAlg = isAlgX } =
       
                                 let fill = CofibrantWkLiftingEquivalence cofibP {{fib₂ = EndMorFib _ tfibp}}
                                            (operadProj₁ p) (HomOpProj₁ p) (EquivProj₁ _ tfibp) εX isAlgX in

                                 record { algebraStruct = operadProj₂ _ ∘ wkLifting.δ fill ;
                                          isAlg = HomOpComp (HomOpProj₂ _) (wkLifting.homδ fill) } 



       --We conclude using the cocylinder factorisation

       module _ {l m} {X : Set l} {{_ : Fib X}} {Y : Set m} {{_ : Fib Y}}
                {f : X → Y} (equivf : Equiv f) where

         algebraInvariantEquiv : Algebra P Y → Algebra P X
         algebraInvariantEquiv algY  = algebraForwardFibration (secCyl f) TrivFibSecCyl
                                       (algebraBackFibration (projCyl f) (TrivFibProjCyl equivf) algY)
