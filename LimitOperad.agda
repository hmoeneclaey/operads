{-# OPTIONS --allow-unsolved-metas #-}

module LimitOperad where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad




--We define the terminal operad

Mon : (A : Set) {{_ : FOSet A}} → Set
Mon A = ⊤

MonFun : arrowAction Mon
MonFun _ _ _ = *

instance
  OpMon : Operad Mon
  OpMon = record
            { functor = MonFun
            ; functorId = λ _ → refl
            ; functorComp = λ _ → refl
            ; id = *
            ; γ = λ _ _ → *
            ; unitLeft = λ _ → refl
            ; unitRight = λ _ → refl
            ; naturalityFiber = λ _ _ _ _ → refl
            ; naturalityBase = λ _ _ _ _ → refl
            ; assoc = λ _ _ _ → refl
            }


TerminalNat : ∀ {k} (P : (A : Set) → {{_ : FOSet A}} → Set k) → Nat P Mon
TerminalNat P _ _ = *

Mon⊤ : ∀ {k} {P : (A : Set) → {{_ : FOSet A}} → Set k} → {{_ : Operad P}} → HomOperad (TerminalNat P)
Mon⊤ = {!!}



--We postulate the pullback of operad

module _ {k l m} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
                 {Q : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad Q}}
                 {R : (A : Set) → {{_ : FOSet A}} → Set m} {{_ : Operad R}}
                 (α : Nat P R) (β : Nat Q R) where

       PullbackOp : (A : Set) → {{_ : FOSet A}} → Set (k ⊔ l ⊔ m)
       PullbackOp A = Pullback (α A) (β A)

       PullbackOpProj₁ : Nat PullbackOp P
       PullbackOpProj₁ A = Pullback.proj₁
       
       PullbackOpProj₂ : Nat PullbackOp Q
       PullbackOpProj₂ A = Pullback.proj₂


module _ {k l m} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
                 {Q : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad Q}}
                 {R : (A : Set) → {{_ : FOSet A}} → Set m} {{_ : Operad R}}
                 {α : Nat P R} (homα : HomOperad α)
                 {β : Nat Q R} (homβ : HomOperad β) where


       instance
         PullbackOperad : Operad (PullbackOp α β)
         PullbackOperad = {!!}

      
       HomProj₁ : HomOperad (PullbackOpProj₁ α β)
       HomProj₁ = ?

       HomProj₂ : HomOperad (PullbackOpProj₂ α β)
       HomProj₂ = ?


