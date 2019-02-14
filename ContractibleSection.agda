module Monoid where

open import Agda.Primitive
open import Data
open import FibrantUniverse
open import FiniteSet
open import Cofibration
open import Operad
open import CofibrantOperad



--In this document we show an operad having section against strongly contractible morphism is cofibrant and acts on loop spaces



--We define operads having section against strongly contractible morphism

StronglyContractibleOp : ∀ {k l} {P : (A : Set) → {{_ : FOSet A}} → Set k}
                                    {Q : (A : Set) → {{_ : FOSet A}} → Set l}
                                    (α : (A : Set) → {{_ : FOSet A}} → P A → Q A)
                                    → Set (lsuc lzero ⊔ k ⊔ l)

StronglyContractibleOp α = (A : Set) → {{_ : FOSet A}} → StronglyContractible (α A)


record SectionOp {k l} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
                       {Q : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad Q}}
                       (α : (A : Set) → {{_ : FOSet A}} → P A → Q A) : Set (lsuc lzero ⊔ k ⊔ l) where
       field
         map : (A : Set) {{_ : FOSet A}} → Q A → P A
         isMorphism : HomOperad map
         isSection : (A : Set) {{_ : FOSet A}} → (c : Q A) → α A (map A c) ≡ c 


sectionStronglyContractibleMap : (P : (A : Set) → {{_ : FOSet A}} → Set) → {{_ : Operad P}} → Setω
sectionStronglyContractibleMap P = ∀ {k} {Q : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad Q}}
                                         {β : (A : Set) → {{_ : FOSet A}} → Q A → P A} (homβ : HomOperad β)
                                         → StronglyContractibleOp β → SectionOp β



--We postulate the pullback of operad

module _ {k l m} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
                 {Q : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad Q}}
                 {R : (A : Set) → {{_ : FOSet A}} → Set m} {{_ : Operad R}}
                 (α : Nat P R) (β : Nat Q R) where

       PullbackOp : (A : Set) → {{_ : FOSet A}} → Set (k ⊔ l ⊔ m)
       PullbackOp A = Pullback (α A) (β A)

       PullbackOpProj₁ : (A : Set) → {{_ : FOSet A}} → PullbackOp A → P A
       PullbackOpProj₁ A = Pullback.proj₁
       
       PullbackOpProj₂ : (A : Set) → {{_ : FOSet A}} → PullbackOp A → Q A
       PullbackOpProj₂ A = Pullback.proj₂


module _ {k l m} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
                 {Q : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad Q}}
                 {R : (A : Set) → {{_ : FOSet A}} → Set m} {{_ : Operad R}}
                 {α : Nat P R} (homα : HomOperad α)
                 {β : Nat Q R} (homβ : HomOperad β) where

       postulate
         instance
           PullbackOperad : Operad (PullbackOp α β)
         HomProj₁ : HomOperad (PullbackOpProj₁ α β)
         HomProj₂ : HomOperad (PullbackOpProj₂ α β)

       sectionLiftingOp : SectionOp (PullbackOpProj₁ α β) → lifting β α
       sectionLiftingOp record { map = δ ;
                                 isMorphism = homδ ;
                                 isSection = secβ}
                      = record { δ = (PullbackOpProj₂ α β) ∘ δ ;
                                 homδ = HomOpComp HomProj₂ homδ ;
                                 equal = λ c → ≡Trans (≡Sym (Pullback.eqPullback (δ _ c)))
                                                      (ap (α _) (secβ _ c)) }





--We show some properties of strongly contractible maps of operads

module _ {k l m} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
                 {Q : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad Q}}
                 {R : (A : Set) → {{_ : FOSet A}} → Set m} {{_ : Operad R}}
                 {α : Nat P R} {β : Nat Q R} where

       StronglyContractiblePullbackOp : StronglyContractibleOp β → StronglyContractibleOp (PullbackOpProj₁ α β)
       StronglyContractiblePullbackOp contrβ A = StronglyContractiblePullback (contrβ A)


module _ {k l} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
               {Q : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad Q}}
               {{fibQ : FibOp Q}}
               {α : Nat P Q} where
                 
       StronglyContractibleTrivialFibrationOp : TrivialFibrationOp α → StronglyContractibleOp α
       StronglyContractibleTrivialFibrationOp tfibα A = StronglyContractibleTrivialFibration
                                                        (record { isFib = TrivialFibration.isFib (tfibα A)  ;
                                                                  isContr = TrivialFibration.isContr (tfibα A) ;
                                                                  isBasis = fibQ {A} })




--We show that an operad having section against strongly contractible map is cofibrant

module _ (∞Mon : (A : Set) → {{_ : FOSet A}} → Set) {{_ : Operad ∞Mon}}
         (∞MonSection : sectionStronglyContractibleMap ∞Mon) where

  Cofib∞Mon : CofibrantOp ∞Mon
  Cofib∞Mon α homα tfibα β homβ = sectionLiftingOp homβ homα
                                  (∞MonSection (HomProj₁ homβ homα)
                                  (StronglyContractiblePullbackOp
                                    (StronglyContractibleTrivialFibrationOp tfibα)))
                                