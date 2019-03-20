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


TerminalMon : ∀ {k} (P : (A : Set) → {{_ : FOSet A}} → Set k) → Nat P Mon
TerminalMon P A = Terminal⊤ (P A)

HomTerminalMon : ∀ {k} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
                 → HomOperad (TerminalMon P)
HomTerminalMon = record { homNat = λ _ → refl ;
                          homId = refl ;
                          homγ = refl }




--We define the pullback of operad

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
         PullbackOperad = ?

      
       HomProj₁ : HomOperad (PullbackOpProj₁ α β)
       HomProj₁ = {!!}

       HomProj₂ : HomOperad (PullbackOpProj₂ α β)
       HomProj₂ = {!!}





--We define the product of operad using pullback over the terminal object


module _ {k l} (P : (A : Set) → {{_ : FOSet A}} → Set k) {{_ : Operad P}}
               (Q : (A : Set) → {{_ : FOSet A}} → Set l) {{_ : Operad Q}} where

       ProdOp : (A : Set) {{_ : FOSet A}} → Set (k ⊔ l)
       ProdOp = PullbackOp (TerminalMon P) (TerminalMon Q)

       ProdOpProj₁ : Nat ProdOp P
       ProdOpProj₁ = PullbackOpProj₁ (TerminalMon P) (TerminalMon Q)

       ProdOpProj₂ : Nat ProdOp Q
       ProdOpProj₂ = PullbackOpProj₂ (TerminalMon P) (TerminalMon Q)


module _ {k l} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
               {Q : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad Q}} where

       instance
         OperadProdOp : Operad (ProdOp P Q)
         OperadProdOp = PullbackOperad HomTerminalMon HomTerminalMon

       HomProdOpProj₁ : HomOperad (ProdOpProj₁ P Q)
       HomProdOpProj₁ = HomProj₁ HomTerminalMon HomTerminalMon

       HomProdOpProj₂ : HomOperad (ProdOpProj₂ P Q)
       HomProdOpProj₂ = HomProj₂ HomTerminalMon HomTerminalMon    
