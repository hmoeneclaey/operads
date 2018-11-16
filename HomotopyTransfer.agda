module HomotopyTransfer where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad





module PullbackOfCollections {k} {P₁ P₂ P₃ : (A : Set) → {{_ : FOSet A}} → Set k}
                             {{_ : Collection P₁}}
                             {{_ : Collection P₂}}
                             {{_ : Collection P₃}}
                             (α : Nat P₁ P₂) {homα : HomCollection Pfun₁ Pfun₂ α}
                             (β : Nat P₃ P₂) {homβ : HomCollection Pfun₃ Pfun₂ β} where


       PullbackColl : (A : Set) → {{_ : FOSet A}} → Set k
       PullbackColl A = Pullback (α A) (β A)


       PullbackCollFun : arrowAction PullbackColl
       PullbackCollFun f ((a , b) , eq) 
                             = ((Pfun₁ f a , Pfun₃ f b ) ,
                                        ≡Trans {y = Pfun₂ f (α _ a)}
                                                       (≡Sym homα)
                                                       (≡Trans {y = Pfun₂ f (β _ b)}
                                                         (ap (Pfun₂ f) eq)
                                                         homβ) )


       instance
         CollectionPullback : Collection PullbackColl PullbackCollFun
         CollectionPullback = record { functorId = λ { ((a , b) , _) → equalPullback (functorId a) (functorId b) } ; 
                                       functorComp = λ { ((a , b) , _) → equalPullback (functorComp a) (functorComp b)} }

       instance
         PullbackOp : {{_ : Operad P₁ Pfun₁}} → {{_ : Operad P₃ Pfun₃}}
                      → α (Fin (s O)) (id {P = P₁} {Pfun = Pfun₁}) ≡ β (Fin (s O)) (id {P = P₃} {Pfun = Pfun₃})
                      → Operad PullbackColl PullbackCollFun
         PullbackOp eq1 = record
                        { id = (id {P = P₁} {Pfun = Pfun₁} , id {P = P₃} {Pfun = Pfun₃}) , eq1
                        ; γ = {!!}
                        ; unitLeft = {!!}
                        ; unitRight = {!!}
                        ; naturalityFiber = {!!}
                        ; naturalityBase = {!!}
                        ; assoc = {!!}
                        }
