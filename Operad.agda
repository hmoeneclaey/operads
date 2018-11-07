
module Operad where

open import Data

--Preliminary about finite sets
open import FiniteSet




--We define small operads

record Operad (P : (A : Set) → {{_ : FOSet A}} → Set)
              (Pfun : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} (f : A → B) {{_ : HomFO f}} → P A → P B) : Set₁ where
              field

                id : P (Fin (s O))

                γ : {A : Set} {{_ : FOSet A}} {B : A → Set} {{_ : {a : A} → FOSet (B a)}} 
                    → P A → ((a : A) → P (B a)) → P (Σ A B)

                functorId : {A : Set} {{_ : FOSet A}} (c : P A)
                            → Pfun (Id {A = A}) {{HomFOId}} c ≡ c

                functorComp : {A B C : Set} {{_ : FOSet A}} {{_ : FOSet B}} {{_ : FOSet C}} 
                              {f : A → B} {g : B → C} {{homf : HomFO f}} {{homg : HomFO g}}
                              → (c : P A) → Pfun g {{homg}} (Pfun f {{homf}} c) ≡ Pfun (g o f) {{HomFOComp homf homg}} c

                unitLeft : {A : Set} {{Afinite : FOSet A}} (c : P A) 
                            → γ c (λ _ → id) ≡ Pfun {{_}} {{_}} (η₂ A) {{HomFOη₂}} c

                unitRight : {B : Fin (s O) → Set} {{Bfinite : {x : Fin (s O)} → FOSet (B x)}} (d : (x : Fin(s O)) → P (B x) {{Bfinite {x}}})
                            → γ id d ≡ Pfun {{_}} {{_}} (η₁ B) {{HomFOη₁ {{Bfinite}}}} (d fzero)


                naturalityFiber : {A : Set} {{_ : FOSet A}} {B₁ B₂ : A → Set} {{_ : {a : A} → FOSet (B₁ a)}} {{_ : {a : A} → FOSet (B₂ a)}} 
                           {F : {a : A} → B₁ a → B₂ a} {{homF : {a : A} → HomFO (F {a})}}
                            (c : P A) (d : (a : A) → P (B₁ a))
                           → Pfun {{_}} {{_}} (Σfun (Id {A = A}) F) {{HomFOΣfun HomFOId homF}} (γ c d) ≡ γ c (λ a → Pfun {{_}} {{_}} (F {a}) {{homF {a}}} (d a) )

                naturalityBase : {A₁ A₂ : Set} {{_ : FOSet A₁}} {{_ : FOSet A₂}} {B : A₂ → Set} {{_ : {a₂ : A₂} → FOSet (B a₂)}}
                          (f : A₁ → A₂) {{homf : HomFO f}}
                          (c : P A₁) (d : (a₂ : A₂) → P (B a₂)) 
                          → Pfun {{_}} {{_}} (Σfun {B₂ = B} f Id) {{HomFOΣfun homf HomFOId}} (γ c (d o f)) ≡ γ (Pfun {{_}} {{_}} f {{homf}} c) d

                assoc : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} {C : Σ A B → Set} {{Cfinite : {x : Σ A B} → FOSet (C x)}}
                        (c : P A) (d : (a : A) → P (B a)) (e : (x : Σ A B) → P (C x)) 
                        → γ (γ c d) e ≡ Pfun {{_}} {{_}} (ψ A B C) {{HomFOψ {{Afinite}} {{Bfinite}} {{Cfinite}} }} (γ c (λ a → γ (d a) (λ b → e (a , b))))





--The monoid operad

Mon : (A : Set) {{_ : FOSet A}} → Set
Mon A = ⊤

MonFun : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} (f : A → B) {{_ : HomFO f}} → Mon A → Mon B
MonFun _ = λ _ → *

MonOperad : Operad Mon MonFun
MonOperad = record
              { id = *
              ; γ = λ _ _ → *
              ; functorId = λ {* → refl}
              ; functorComp = λ _ → refl
              ; unitLeft = λ _ → refl 
              ; unitRight = λ _ → refl
              ; naturalityFiber = λ _ _ → refl
              ; naturalityBase = λ _ _ _ → refl
              ; assoc = λ _ _ _ → refl
              }




--The endomorphism operad

End : (X : Set) (A : Set) {{_ : FOSet A}} → Set
End X A = (A → X) → X

EndFun : (X : Set) {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} (f : A → B) {{_ : HomFO f}} → End X A → End X B
EndFun X f = λ c g → c (g o f)

EndOperad : (X : Set) → Operad (End X) (EndFun X)
EndOperad X = record
                { id = λ c → c fzero
                ; γ = λ c D → λ e → c (λ a → D a (λ b → e (a , b)))
                ; functorId = λ _ → refl
                ; functorComp = λ _ → refl
                ; unitLeft = λ _ → refl
                ; unitRight = λ _ → refl
                ; naturalityFiber = λ _ _ → refl
                ; naturalityBase = λ _ _ _ → refl
                ; assoc = λ _ _ _ → refl
                }

