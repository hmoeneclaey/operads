{-# OPTIONS --allow-unsolved-metas #-}

module LoopSpace where

open import Agda.Primitive
open import Data
open import FibrantUniverse
open import FiniteSet
open import MorphismFiniteSet
open import Operad
open import Cofibration





--first some preliminary constructions on finite sets

Succ : (A : Set) → {{_ : FOSet A}} → Set
Succ A = A ∨ ⊤

min : {A : Set} → {{_ : FOSet A}} → Succ A
min ⦃ record { cardinal = O ; funFO = f ; isIsoFO = isof } ⦄ = right *
min ⦃ record { cardinal = s |A| ; funFO = f ; isIsoFO = isof } ⦄ = left (iso.inv isof fzero)

max : {A : Set} → {{_ : FOSet A}} → Succ A
max = right *

fmax : {n : ℕ} → Fin (s n)
fmax {O} = fzero
fmax {s n} = fsucc (fmax {n})



-- We show that Succ (Fin n) is isomorphic to Fin (s n) 

Fin⊤SuccAux : {n : ℕ} → Fin n → Fin (s n)
Fin⊤SuccAux fzero = fzero
Fin⊤SuccAux (fsucc x) = fsucc (Fin⊤SuccAux x)

Fin⊤Succ : {n : ℕ} → Succ (Fin n) → Fin (s n)
Fin⊤Succ = ∨Elim Fin⊤SuccAux (λ _ → fmax)

invFin⊤Succ : {n : ℕ} → Fin (s n) → Succ (Fin n)
invFin⊤Succ {O} fzero = right *
invFin⊤Succ {s n} fzero = left fzero
invFin⊤Succ {s n} (fsucc x) = ∨Nat fsucc Id (invFin⊤Succ x)

invFun⊤SuccMax : {n : ℕ} → right * ≡ invFin⊤Succ {n} fmax 
invFun⊤SuccMax {O} = refl
invFun⊤SuccMax {s n} = ap (∨Nat fsucc Id) (invFun⊤SuccMax {n})

Fin⊤SuccInvLeftAux : {n : ℕ} (b : Succ (Fin n)) → fsucc (Fin⊤Succ b) ≡ Fin⊤Succ (∨Nat fsucc Id b)
Fin⊤SuccInvLeftAux (left fzero) = refl
Fin⊤SuccInvLeftAux (left (fsucc x)) = refl
Fin⊤SuccInvLeftAux (right *) = refl

Fin⊤SuccInvLeft : {n : ℕ} (b : Fin (s n)) → b ≡ Fin⊤Succ (invFin⊤Succ b)
Fin⊤SuccInvLeft {O} fzero = refl
Fin⊤SuccInvLeft {s n} fzero = refl
Fin⊤SuccInvLeft {s n} (fsucc b) = ≡Trans (ap fsucc (Fin⊤SuccInvLeft b))
                                         (Fin⊤SuccInvLeftAux (invFin⊤Succ b))

Fin⊤SuccInvRight : {n : ℕ} (b : Succ (Fin n)) → b ≡ invFin⊤Succ(Fin⊤Succ b)
Fin⊤SuccInvRight {O} (right *) = refl
Fin⊤SuccInvRight {s n} (left fzero) = refl
Fin⊤SuccInvRight {s n} (left (fsucc x)) = ap (∨Nat fsucc Id) (Fin⊤SuccInvRight (left x))
Fin⊤SuccInvRight {s n} (right *) = invFun⊤SuccMax

isoFin⊤Succ : {n : ℕ} → iso (Fin⊤Succ {n}) 
isoFin⊤Succ = record { inv = invFin⊤Succ ;
                       invLeft = Fin⊤SuccInvLeft ;
                       invRight = Fin⊤SuccInvRight } 



--We show that the successor of a finite set is a finite set, and construct the two injective morphisms from A to Succ A

instance
    Fin∨⊤ : {A : Set} → {{_ : FOSet A}} → FOSet (Succ A) 
    Fin∨⊤ {{ record { cardinal = |A| ;
                    funFO = f ;
                    isIsoFO = isof } }}
         = record { cardinal = s |A| ;
                    funFO = Fin⊤Succ o ∨Nat f Id ;
                    isIsoFO = isoComp {f = ∨Nat f Id} (iso∨Nat isof isoId) (isoFin⊤Succ {|A|}) }
                    

inc₀ : {A : Set} {{_ : FOSet A}} → A → Succ A
inc₀ a = left a

inc₁ : {A : Set} {{_ : FOSet A}} → A → Succ A
inc₁ {A} a = iso.inv isIsoFO (fsucc (funFO a))

inc₁morphism : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}}
         → (f : A → B) → HomFO f → {a : A} → inc₁ (f a) ≡ ∨Nat f Id (inc₁ a)
inc₁morphism f = {!!}



--We define string of composable paths

record composablePath {k} (X : Set k) (A : Set) {{_ : FOSet A}} : Set k where
  field
    point : Succ A → X
    path : (a : A) → point (inc₀ a) ~~> point (inc₁ a)


≡ComposablePathAux : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {P Q : composablePath X A}
                     → composablePath.point P ≡ composablePath.point Q
                     → ((a : A) (i : I) → composablePath.path P a $ i ≡ composablePath.path Q a $ i)
                     → P ≡ Q
                     
≡ComposablePathAux {P = P} refl eqPath = ap (λ H → record { point = composablePath.point P ; path = H })
                                            (funext (λ a → ≡Path (eqPath a)))


≡ComposablePath : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {P Q : composablePath X A}
                  → ((a : Succ A) → composablePath.point P a ≡ composablePath.point Q a)
                  → ((a : A) (i : I) → composablePath.path P a $ i ≡ composablePath.path Q a $ i)
                  → P ≡ Q
                  
≡ComposablePath eqPoint eqPath = ≡ComposablePathAux (funext eqPoint) eqPath


firstPoint : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} → composablePath X A → X
firstPoint p = composablePath.point p min

lastPoint : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} → composablePath X A → X
lastPoint p = composablePath.point p max

composableHrefl : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} → X → composablePath X A
composableHrefl x = record { point = λ _ → x ; path = λ _ → hrefl }

loopComposable : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {x : X}
                 → (A → x ~~> x) → composablePath X A
loopComposable {x = x} f = record { point = λ _ → x ; path = f }



--Now we show various functorialities of the string of composable paths

module _ {k} {X : Set k} where

  composablePathFunct : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}}
                        (f : A → B) → HomFO f → composablePath X B → composablePath X A
                        
  composablePathFunct f homf record { point = g ;
                                      path = G }
                           = record { point = g o ∨Nat f Id ;
                                      path = λ a → endpointPath (G (f a)) refl (ap g (inc₁morphism f homf)) }


  composablePathFunctId : {A : Set} {{_ : FOSet A}} {a : composablePath X A}
                          → composablePathFunct Id HomFOId a ≡ a
                        
  composablePathFunctId {a = record { point = f ; path = F }} = ≡ComposablePath (λ { (left _) → refl ; (right _) → refl})
                                                                                (λ _ _ → refl)


  composablePathFunctComp : {A B C : Set} {{_ : FOSet A}} {{_ : FOSet B}} {{_ : FOSet C}}
                            {f : A → B} {g : B → C} (homf : HomFO f) (homg : HomFO g) (c : composablePath X C)
                            → composablePathFunct f homf (composablePathFunct g homg c) ≡ composablePathFunct (g o f) (HomFOComp homf homg) c

  composablePathFunctComp homf homg record { point = h ; path = H } = ≡ComposablePath (λ { (left _) → refl ; (right _) → refl})
                                                                                      (λ _ _ → refl)



module _ {k} {X : Set k} {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}}
         (f : A → B) (homf : HomFO f) where

       minMorphism : ∨Nat f Id (min {A}) ≡ min {B}
       minMorphism = {!!}

       composablePathFunctFirstPoint : (p : composablePath X B) → firstPoint (composablePathFunct f homf p) ≡ firstPoint p
       composablePathFunctFirstPoint record { point = g ; path = G } = ap g minMorphism

       composablePathFunctHrefl : {x : X} → composablePathFunct f homf (composableHrefl x) ≡ composableHrefl x
       composablePathFunctHrefl = ≡ComposablePath (λ _ → refl) (λ _ _ → refl)



--We define the path operad

module _ {k} (X : Set k) where

  record PathOp (A : Set) {{_ : FOSet A}} : Set k where
    field
      fun : (p : composablePath X A) → firstPoint p ~~> lastPoint p
      equality : (x : X) → fun (composableHrefl x) ≡ hrefl


≡PathOpAux : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {P Q : PathOp X A}
          → PathOp.fun P ≡ PathOp.fun Q → P ≡ Q
          
≡PathOpAux {P = P} refl = ap (λ H → record { fun = PathOp.fun P ; equality = H }) (funext (λ _ → UIP))


≡PathOp : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {P Q : PathOp X A}
          → ((p : composablePath X A) → PathOp.fun P p ≡ PathOp.fun Q p) → P ≡ Q
          
≡PathOp equalFun = ≡PathOpAux (funext equalFun)



module _ {k} {X : Set k} where


  PathOpFun : {A B : Set} → {{_ : FOSet A}} → {{_ : FOSet B}}
              → (f : A → B) → HomFO f → PathOp X A → PathOp X B

  PathOpFun f homf record { fun = ϕ ; equality = eq } =
                   record { fun = λ p → endpointPath  (ϕ (composablePathFunct f homf p))
                                                      (composablePathFunctFirstPoint f homf p)
                                                      refl  ;
                            equality = λ x → ≡Path (λ i → ≡Trans {y = ϕ (composableHrefl x) $ i}
                                                                 (ap (λ H → ϕ H $ i) (composablePathFunctHrefl f homf))
                                                                 (ap (λ p → p $ i) (eq x))) }


  instance
    OperadPathOp : Operad (PathOp X)
    
    OperadPathOp = record
                     { functor = PathOpFun
                     
                     ; functorId = λ { record { fun = ϕ ; equality = _ }
                                       → ≡PathOp λ p → ≡Path (λ i → ap (λ H → ϕ H $ i) composablePathFunctId)}
                     
                     ; functorComp = λ { {homf = homf} {homg = homg} record { fun = ϕ ; equality = _ }
                                         → ≡PathOp (λ p → ≡Path (λ i → ap (λ H → ϕ H $ i) (composablePathFunctComp homf homg p)))}
                     
                     ; id = record { fun = λ { record { point = f ; path = F } → F fzero} ;
                                     equality = λ _ → refl }
                     
                     ; γ = {!!}
                     ; unitLeft = {!!}
                     ; unitRight = {!!}
                     ; naturalityFiber = {!!}
                     ; naturalityBase = {!!}
                     ; assoc = {!!}
                     }



--We define the morphisms from the path operad to the endomorphism operads


  PathOpToEnd : (x : X) → Nat (PathOp X) (End (x ~~> x))
  
  PathOpToEnd _ _ ϕ p = PathOp.fun ϕ (loopComposable p)


  HomPathOpToEnd : (x : X) → HomOperad (PathOpToEnd x)
  
  HomPathOpToEnd = {!!}



--We prove the path operad is strongly contractible


  StronglyContractiblePathOp : {{_ : Fib X}} {A : Set} {{_ : FOSet A}} → StronglyContractible (PathOp X A)
  
  StronglyContractiblePathOp = {!!}
