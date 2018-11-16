module HomotopyTransfer where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad





module PullbackOfCollections {k} {P₁ P₂ P₃ : (A : Set) → {{_ : FOSet A}} → Set k}
                             {{colP₁ : Collection P₁}}
                             {{_ : Collection P₂}}
                             {{_ : Collection P₃}}
                             (α : Nat P₁ P₂) {homα : HomCollection α}
                             (β : Nat P₃ P₂) {homβ : HomCollection β} where


       PullbackColl : (A : Set) → {{_ : FOSet A}} → Set k
       PullbackColl A = Pullback (α A) (β A)


       PullbackCollFun : arrowAction PullbackColl
       PullbackCollFun f ((a , b) , eq) 
                             = ((functor f a , functor f b ) ,
                                        ≡Trans {y = functor f (α _ a)}
                                                       (≡Sym homα)
                                                       (≡Trans {y = functor f (β _ b)}
                                                         (ap (functor f) eq)
                                                         homβ) )


       instance
         CollectionPullback : Collection PullbackColl
         CollectionPullback = record { functor = PullbackCollFun ;
                                       functorId = λ { ((a , b) , _) → equalPullback (functorId a) (functorId b) } ;
                                       functorComp = λ { ((a , b) , _) → equalPullback (functorComp a) (functorComp b)} }



       instance
         PullbackOp : {{_ : Operad P₁}} → {{_ : Operad P₃}}
                      → α (Fin (s O)) id ≡ β (Fin (s O)) id
                      → ({A : Set} → {{_ : FOSet A}} → {B : A → Set} → {{_ : {a : A} → FOSet (B a)}}
                            → {c₁ : P₁ A} → {c₃ : P₃ A} → {d₁ : (a : A) → P₁ (B a)} → {d₃ : (a : A) → P₃ (B a)}
                            → α A c₁ ≡ β A c₃ → ((a : A) → α _ (d₁ a) ≡ β _ (d₃ a))
                            → α _ (γ c₁ d₁) ≡  β _ (γ c₃ d₃))
                      → Operad PullbackColl

         PullbackOp {{opP₁}} {{opP₂}} eqId eqγ = record

                         { id = (id , id) , eqId

                        ; γ = λ c d → (γ (proj₁ c) (proj₁ o d) , γ (proj₂ c) (proj₂ o d))
                                      , eqγ (equalProj c) (λ a → equalProj (d a))

                        ; unitLeft = λ { ((c₁ , c₂) , eq) → equalPullback (unitLeft c₁) (unitLeft c₂)}

                        ; unitRight = λ d → equalPullback (≡Trans {y = functor (η₁ _) {{HomFOη₁}} (proj₁ (d fzero))} (unitRight (proj₁ o d)) {!!})
                                                          (≡Trans {y = functor (η₁ _) {{HomFOη₁}} (proj₂ (d fzero))} (unitRight (proj₂ o d)) {!!})

                        ; naturalityFiber = {!!}
                        ; naturalityBase = {!!}
                        ; assoc = {!!}
                        }

