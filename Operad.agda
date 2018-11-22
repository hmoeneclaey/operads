 
module Operad where

open import Agda.Primitive
open import Data

--Preliminary about finite sets
open import FiniteSet





--First some definition about collections

arrowAction : ∀ {k} (P : (A : Set) → {{_ : FOSet A}} → Set k) → Set (lsuc lzero ⊔ k)
arrowAction P = {A B : Set} {Afinite : FOSet A} {Bfinite : FOSet B} 
                      (f : A → B) {{_ : HomFO {{Afinite}} {{Bfinite}} f}} 
                      → P A {{Afinite}} → P B {{Bfinite}}

Nat : ∀ {k l} (P₁ : (A : Set) → {{_ : FOSet A}} → Set k) (P₂ : (A : Set) → {{_ : FOSet A}} → Set l) → Set (lsuc lzero ⊔ (k ⊔ l))
Nat P₁ P₂ = (A : Set) → {{_ : FOSet A}} → P₁ A → P₂ A



--We define operads

record Operad {k} (P : (A : Set) → {{_ : FOSet A}} → Set k) : Set (lsuc k) where

              field            

                functor : arrowAction P

                functorId : {A : Set} {{_ : FOSet A}} (c : P A)
                           → functor (Id {A = A}) c ≡ c

                functorComp : {A B C : Set} {{_ : FOSet A}} {{_ : FOSet B}} {{_ : FOSet C}} 
                              {f : A → B} {g : B → C} {{homf : HomFO f}} {{homg : HomFO g}}
                              → (c : P A) → functor g {{homg}} (functor f c) ≡ functor (g o f) {{HomFOComp f g}} c

                id : P (Fin (s O))

                γ : {A : Set} {{_ : FOSet A}} {B : A → Set} {{_ : {a : A} → FOSet (B a)}} 
                    → P A → ((a : A) → P (B a)) → P (Σ A B)

                unitLeft : {A : Set} {{_ : FOSet A}} 
                           (c : P A) 
                           → γ c (λ _ → id) ≡ functor (η₂ A) c

                unitRight : {B : Fin (s O) → Set} {{_ : {x : Fin (s O)} → FOSet (B x)}}
                            (d : (x : Fin(s O)) → P (B x))
                            → γ id d ≡ functor (η₁ B) {{HomFOη₁}} (d fzero)

                naturalityFiber : {A : Set} {{_ : FOSet A}} 
                           {B₁ B₂ : A → Set} {{_ : {a : A} → FOSet (B₁ a)}} {{_ : {a : A} → FOSet (B₂ a)}} 
                           (F : {a : A} → B₁ a → B₂ a) {{_ : {a : A} → HomFO (F {a})}}
                           (c : P A) (d : (a : A) → P (B₁ a))
                           → functor (Σfun (Id {A = A}) F) {{HomFOΣfun}} (γ c d) ≡ γ c (λ a → functor (F {a}) (d a) )

                naturalityBase : {A₁ A₂ : Set} {{_ : FOSet A₁}} {{_ : FOSet A₂}} 
                          {B : A₂ → Set} {{_ : {a₂ : A₂} → FOSet (B a₂)}}
                          (f : A₁ → A₂) {{_ : HomFO f}}
                          (c : P A₁) (d : (a₂ : A₂) → P (B a₂)) 
                          → functor (Σfun {B₂ = B} f Id) {{HomFOΣfun}} (γ c (d o f)) ≡ γ (functor f c) d

                assoc : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} 
                        {C : Σ A B → Set} {{Cfinite : {x : Σ A B} → FOSet (C x)}}
                        (c : P A) (d : (a : A) → P (B a)) (e : (x : Σ A B) → P (C x)) 
                        → γ (γ c d) e ≡ functor (ψ A B C) {{HomFOψ}} (γ c (λ a → γ (d a) (λ b → e (a , b))))


open Operad {{...}} public


record HomOperad {k l} {P₁ : (A : Set) → {{_ : FOSet A}} → Set k} {P₂ : (A : Set) → {{_ : FOSet A}} → Set l}
                 {{_ : Operad P₁}} {{_ : Operad P₂}}
                 (α : Nat P₁ P₂) : Set (lsuc lzero ⊔ (k ⊔ l)) where
       field

         HomCollection : {A : Set} {{_ : FOSet A}} {B : Set} {{_ : FOSet B}} {f : A → B} {{homf : HomFO f}}
                         → {c : P₁ A} → α _ (functor f c) ≡ functor f (α _ c)

         HomOperadId : α _ id ≡ id

         HomOperadγ : {A : Set} {{_ : FOSet A}} {B : A → Set} {{_ : {a : A} → FOSet (B a)}}
                      {c : P₁ A} {d : (a : A) → P₁ (B a)}
                      → α _ (γ c d) ≡ γ (α _ c) (λ a → α _ (d a))



module _  {k l m} {P₁ : (A : Set) → {{_ : FOSet A}} → Set k} {P₂ : (A : Set) → {{_ : FOSet A}} → Set l} {P₃ : (A : Set) → {{_ : FOSet A}} → Set m} where 

       idtest : {A : Set} → A → A
       idtest {A} = λ x → x

       _∘_ : Nat P₂ P₃ → Nat P₁ P₂ → Nat P₁ P₃
       (β ∘ α) A = (β A) o (α A)

       
       HomOpComp : {{_ : Operad P₁}} {{_ : Operad P₂}} {{_ : Operad P₃}} → {α : Nat P₁ P₂} → {β : Nat P₂ P₃}  → HomOperad β →  HomOperad α  → HomOperad (β ∘ α)

       HomOpComp {α = α} {β = β}
                 record { HomCollection = homNatβ ; HomOperadId = homIdβ ; HomOperadγ = homγβ }
                 record { HomCollection = homNatα ; HomOperadId = homIdα ; HomOperadγ = homγα } =
                 record { HomCollection = ≡Trans (ap (β _) homNatα) homNatβ ;
                          HomOperadId = ≡Trans (ap (β _) homIdα) homIdβ ;
                          HomOperadγ = ≡Trans (ap (β _) homγα) homγβ }


{-
--The monoid operad

Mon : (A : Set) {{_ : FOSet A}} → Set
Mon A = ⊤

MonFun : arrowAction Mon
MonFun _ = λ _ → *

{-
instance
  CollMon : Collection Mon
  CollMon = record { functor = MonFun ;
                     functorId = λ _ → refl ;
                     functorComp = λ _ → refl }
-}
instance
  postulate
    OpMon : Operad Mon
{-
OpMon = record
              { id = *
              ; γ = λ _ _ → *
              ; unitLeft = λ _ → refl
              ; unitRight = λ _ → refl
              ; naturalityFiber = λ _ _ _ → refl
              ; naturalityBase = λ _ _ _ → refl
              ; assoc = λ _ _ _ → refl
              }
-}
-}



--The endomorphism operad

End : ∀ {k} (X : Set k) (A : Set) {{_ : FOSet A}} → Set k
End X A = (A → X) → X

EndFun : ∀ {k} (X : Set k) → arrowAction (End X)
EndFun X f = λ c g → c (g o f)

instance
  OpEnd : ∀ {k} {X : Set k} → Operad (End X)
  OpEnd = record
              { functor = λ f c g → c (g o f)
              ; functorId = λ _ → refl
              ; functorComp = λ _ → refl
              ; id = λ c → c fzero
              ; γ = λ c d f → c (λ a → d a (λ b → f (a , b)))
              ; unitLeft = λ _ → refl
              ; unitRight = λ _ → refl
              ; naturalityFiber = λ _ _ _ → refl
              ; naturalityBase = λ _ _ _ → refl
              ; assoc = λ _ _ _ → refl
              }


record Algebra {k l} (P : (A : Set) → {{_ : FOSet A}} → Set k) {{_ : Operad P}} (X : Set l) : Set (lsuc lzero ⊔ (k ⊔ l)) where
  field
    algebraStruct : Nat P (End X)
    isAlg : HomOperad algebraStruct




