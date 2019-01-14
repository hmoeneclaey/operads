module OperadCocylinder where

open import Agda.Primitive
open import Data
open import FiniteSet
open import MorphismFiniteSet
open import Operad
open import FibrantUniverse


--In this file we define the cocylinder of operads. It takes ~1 min to typecheck


module _ {k l} {P₁ : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P₁}} {{_ : {A : Set} → {{_ : FOSet A}} → Fib (P₁ A)}}
         {P₂ : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad P₂}} {{_ : {A : Set} → {{_ : FOSet A}} → Fib (P₂ A)}}
         (α : Nat P₁ P₂) where

       cocylinderOp : (A : Set) → {{_ : FOSet A}} → Set (k ⊔ l)
       cocylinderOp A = cocylinder (α A)

       projCylOp : Nat cocylinderOp P₂
       projCylOp A = projCyl (α A)

       secCylOp : Nat cocylinderOp P₁
       secCylOp A = secCyl (α A)



module _ {k l} {P₁ : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P₁}} {{_ : {A : Set} → {{_ : FOSet A}} → Fib (P₁ A)}}
         {P₂ : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad P₂}} {{_ : {A : Set} → {{_ : FOSet A}} → Fib (P₂ A)}}
         {α : Nat P₁ P₂} {{homα : HomOperad α}} where

       instance
         OperadCocylinder : Operad (cocylinderOp α)
         OperadCocylinder = record
                              { functor = λ { f homf (cyl x , y , p) → cyl functor f homf x , functor f homf y ,
                                                                      [ (λ i → functor f homf (p $ i)) ,
                                                                           ≡Trans (ap (functor f homf) (eqe₀ p))
                                                                                  (≡Sym (HomOperad.homNat homα homf)) ,
                                                                           ap (functor f homf) (eqe₁ p) ]}

                              ; functorId = λ _ → ≡cocylinder (functorId _) (functorId _) (λ _ → functorId _)

                              ; functorComp = λ _ → ≡cocylinder (functorComp _) (functorComp _) (λ _ → functorComp _)
                              
                              ; id = cyl id , id , [ (λ i → id) , (≡Sym (HomOperad.homId homα)) , refl ]
                              
                              ; γ = λ c d → cyl (γ (cocylinder.piX c) (cocylinder.piX o d)) ,
                                                (γ (cocylinder.piY c) (cocylinder.piY o d)) ,
                                                ([ (λ i → γ (cocylinder.path c $ i) λ a → cocylinder.path (d a) $ i) ,
                                                      ≡Trans (ap₂ γ (eqe₀ (cocylinder.path c))
                                                                    (funext (λ a → eqe₀ (cocylinder.path (d a)))))
                                                             (≡Sym (HomOperad.homγ homα)) ,
                                                      ap₂ γ (eqe₁ (cocylinder.path c))
                                                            (funext (λ a → eqe₁ (cocylinder.path (d a)))) ]) 
                              
                              ; unitLeft = λ _ → ≡cocylinder (unitLeft _) (unitLeft _) (λ _ → unitLeft _)
                              
                              ; unitRight = λ d → ≡cocylinder (unitRight (cocylinder.piX o d)) (unitRight (cocylinder.piY o d))
                                                              (λ i → unitRight (λ a → cocylinder.path (d a) $ i))

                              ; naturalityFiber = λ F homF c d → ≡cocylinder (naturalityFiber F homF (cocylinder.piX c) (cocylinder.piX o d))
                                                                             (naturalityFiber F homF (cocylinder.piY c) (cocylinder.piY o d))
                                                                             (λ i → naturalityFiber F homF (cocylinder.path c $ i)
                                                                                                     (λ a → cocylinder.path (d a) $ i))
                              
                              ; naturalityBase = λ f homf c d → ≡cocylinder (naturalityBase f homf (cocylinder.piX c) (cocylinder.piX o d))
                                                                            (naturalityBase f homf (cocylinder.piY c) (cocylinder.piY o d))
                                                                            (λ i → naturalityBase f homf (cocylinder.path c $ i)
                                                                                                  (λ a → cocylinder.path (d a) $ i))
                              
                              ; assoc = λ c d e → ≡cocylinder (assoc (cocylinder.piX c) (cocylinder.piX o d) (cocylinder.piX o e))
                                                              (assoc (cocylinder.piY c) (cocylinder.piY o d) (cocylinder.piY o e))
                                                              (λ i → assoc (cocylinder.path c $ i) (λ a → cocylinder.path (d a) $ i)
                                                                           (λ x → cocylinder.path (e x) $ i))
                              
                              }
