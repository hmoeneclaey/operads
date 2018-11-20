module HomotopyTransfer where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad





module PullbackOfCollections {k} {P₁ P₂ P₃ : (A : Set) → {{_ : FOSet A}} → Set k}
                             {{colP₁ : Collection P₁}}
                             {{colP₂ : Collection P₂}}
                             {{colP₃ : Collection P₃}}
                             (α : Nat P₁ P₂) {homα : HomCollection α}
                             (β : Nat P₃ P₂) {homβ : HomCollection β} where


       PullbackColl : (A : Set) → {{_ : FOSet A}} → Set k
       PullbackColl A = Pullback (α A) (β A)


       PullbackCollFun : arrowAction PullbackColl
       PullbackCollFun f ((a , b) , eq) 
                             = ((functor f a , functor f b ) ,
                                        ≡Trans {y = functor f (α _ a)}
                                                       (≡Sym (homα f a))
                                                       (≡Trans {y = functor f (β _ b)}
                                                         (ap (functor f) eq)
                                                         (homβ f b)) )


       instance
         CollectionPullback : Collection PullbackColl
         CollectionPullback = record { functor = PullbackCollFun ;
                                       functorId = λ { ((a , b) , _) → equalPullback (functorId a) (functorId b) } ;
                                       functorComp = λ { ((a , b) , _) → equalPullback (functorComp a) (functorComp b)} }


       operadProj₁ : Nat PullbackColl P₁
       operadProj₁ A x = proj₁ x

       operadProj₂ : Nat PullbackColl P₃
       operadProj₂ A x = proj₂ x

       
       HomCollProj₁ : HomCollection operadProj₁
       HomCollProj₁ f ((_ , _) , _) = refl

       HomCollProj₂ : HomCollection operadProj₂
       HomCollProj₂ f ((_ , _) , _) = refl


       module PullbackOfOperads {{_ : Operad P₁}} {{_ : Operad P₃}}
                      (eqId : α (Fin (s O)) id ≡ β (Fin (s O)) id)
                      (eqγ : {A : Set} → {{_ : FOSet A}} → {B : A → Set} → {{_ : {a : A} → FOSet (B a)}}
                            → {c₁ : P₁ A} → {c₃ : P₃ A} → {d₁ : (a : A) → P₁ (B a)} → {d₃ : (a : A) → P₃ (B a)}
                            → α A c₁ ≡ β A c₃ → ((a : A) → α _ (d₁ a) ≡ β _ (d₃ a))
                            → α _ (γ c₁ d₁) ≡  β _ (γ c₃ d₃))
                            where


                      instance                        
                        PullbackOp : Operad PullbackColl
                        PullbackOp = record

                                   { id = (id , id) , eqId
              
                                   ; γ = λ c d → (γ (proj₁ c) (proj₁ o d) , γ (proj₂ c) (proj₂ o d))
                                      , eqγ (equalProj c) (λ a → equalProj (d a))

                                   ; unitLeft = λ { ((c₁ , c₂) , eq) → equalPullback (unitLeft c₁) (unitLeft c₂)}

                                   ; unitRight = λ {B} d → equalPullback (≡Trans (unitRight (proj₁ o d)) (HomCollProj₁ (η₁ B) (d fzero)))
                                                              (≡Trans (unitRight (proj₂ o d)) (HomCollProj₂ (η₁ B) (d fzero)))

                                   ; naturalityFiber = λ F c d → equalPullback (≡Trans (naturalityFiber F (proj₁ c) (proj₁ o d))
                                                                            (ap (γ (proj₁ c)) (funext (λ a → HomCollProj₁ F (d a)))))
                                                                    (≡Trans (naturalityFiber F (proj₂ c) (proj₂ o d))
                                                                            (ap (γ (proj₂ c)) (funext (λ a → HomCollProj₂ F (d a)))))

                                   ; naturalityBase = λ f c d → equalPullback (≡Trans (naturalityBase f (proj₁ c) (proj₁ o d))
                                                                           (ap (λ c₁ → γ c₁ (proj₁ o d)) (HomCollProj₁ f c)))
                                                                   (≡Trans (naturalityBase f (proj₂ c) (proj₂ o d))
                                                                           (ap (λ c₁ → γ c₁ (proj₂ o d)) (HomCollProj₂ f c)))

                                   ; assoc = λ c d e → equalPullback (assoc (proj₁ c) (proj₁ o d) (proj₁ o e))
                                                          (assoc (proj₂ c) (proj₂ o d) (proj₂ o e))
                                   }

                      HomOpProj₁ : {!!}
                      HomOpProj₁ = {!!}
             




