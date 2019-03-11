{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-eta-equality #-}

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


--left a₁ << left a₂ → a₁ << a₂



--We develop a bit of theory for total order.

<Trans : {n : ℕ} {x y z : Fin n} → x << y → y << z → x << z
<Trans {.(s _)} {fzero} {fzero} {z} ()
<Trans {.(s _)} {fzero} {fsucc y} {fzero} _ () 
<Trans {.(s _)} {fzero} {fsucc y} {fsucc z} _ _ = *
<Trans {.(s _)} {fsucc x} {fzero} {z} () 
<Trans {.(s _)} {fsucc x} {fsucc y} {fzero} _ ()
<Trans {.(s _)} {fsucc x} {fsucc y} {fsucc z} = <Trans {x = x} {y} {z}

<<Trans : {A : Set} {{_ : FOSet A}} {x y z : A} → x << y → y << z → x << z
<<Trans {x = x} {y} {z} = <Trans {x = funFO x} {y = funFO y} {z = funFO z}

_≤_ : {A : Set} {{_ : FOSet A}} (a b : A) → Set
a ≤ b = (a ≡ b) ∨ (a << b)

<<Total : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {x y : A} → x << y → y ≤ x → X
<<Total {x = x} eq₁ (left refl) = efql (<<Irefl x eq₁)
<<Total {x = x} {y} eq₁ (right eq₂) = efql (<<Irefl x (<<Trans {x = x} {y = y} {z = x} eq₁ eq₂))

≤Total : {A : Set} {{_ : FOSet A}} {x y : A} → ¬ (y << x) → x ≤ y
≤Total = {!!}

≤<Trans : {A : Set} {{_ : FOSet A}} {x y z : A} → x ≤ y → y << z → x << z
≤<Trans (left refl) eq₂ = eq₂
≤<Trans {x = x} {y} {z} (right eq₁) eq₂ = <<Trans {x = x} {y} {z} eq₁ eq₂ 

isSuccessor : {A : Set} {{_ : FOSet A}} (a b : A) → Set
isSuccessor {A} a b = (a << b) ∧ ((c : A) → a << c → b ≤ c)

isMin : {A : Set} {{_ : FOSet A}} → A → Set
isMin {A} a = (a₁ : A) → a ≤ a₁

isMax : {A : Set} {{_ : FOSet A}} → A → Set
isMax {A} a = (a₁ : A) → a₁ ≤ a

fmaxIsMaxAux : {n : ℕ} {x : Fin n} → Fin⊤SuccAux x < fmax
fmaxIsMaxAux {x = fzero} = *
fmaxIsMaxAux {x = fsucc x} = fmaxIsMaxAux {x = x}

fmaxIsMax : {n : ℕ} {x : Fin n} → Fin⊤Succ (left x) < fmax
fmaxIsMax {x = fzero} = *
fmaxIsMax {x = fsucc x} = fmaxIsMaxAux {x = x}

maxIsMax : {A : Set} {{_ : FOSet A}} → isMax (max {A})
maxIsMax (left x) = right (fmaxIsMax {x = funFO x})
maxIsMax (right *) = left refl

succIsSucc : {A : Set} {{_ : FOSet A}} → {a : A} → inc₀ a << inc₁ a
succIsSucc = {!!}

inc₀Order : {A : Set} {{_ : FOSet A}} → {a₁ a₂ : A} → a₁ << a₂ → inc₀ a₁ << inc₀ a₂
inc₀Order eq = {!!}

inc₀OrderConverse : {A : Set} {{_ : FOSet A}} → {a₁ a₂ : A} → inc₀ a₁ << inc₀ a₂ →  a₁ << a₂
inc₀OrderConverse = {!!}

inc₁Order : {A : Set} {{_ : FOSet A}} → {a₁ a₂ : A} → a₁ << a₂ → inc₁ a₁ << inc₁ a₂
inc₁Order = {!!}

--isSuccessorCorrect : {A : Set} {{_ : FOSet A}} {a b : A} → isSuccessor a b ↔ (inc₀ b ≡ inc₁ a)
--isSuccessorCorrect = {!!}

inc₁morphism : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}}
         → (f : A → B) → HomFO f → {a : A} → inc₁ (f a) ≡ ∨Nat f Id (inc₁ a)
inc₁morphism f = {!!}


minIsMin : {A : Set} {{_ : FOSet A}} → isMin (min {A})
minIsMin {A} ⦃ record { cardinal = O ; funFO = f ; isIsoFO = isof } ⦄ = λ { (left x) → {!!} ; (right *) → left refl}
minIsMin {A} ⦃ record { cardinal = s |A| ; funFO = f ; isIsoFO = isof } ⦄ (left x) =  {!!}
minIsMin {A} ⦃ record { cardinal = s |A| ; funFO = f ; isIsoFO = isof } ⦄ (right *) =
             maxIsMax ⦃ record { cardinal = s |A| ; funFO = f ; isIsoFO = isof } ⦄  (left (iso.inv isof fzero))


isMinDef : {A : Set} {{_ : FOSet A}} {x : Succ A} → isMin x → x ≡ min {A}
isMinDef = {!!}




module _ {A : Set} {B : A → Set} {{_ : FOSet A}} {{_ : {a : A} → FOSet (B a)}} where

  ΣFirst : {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} → a₁ << a₂ → ord (Σ A B) (a₁ , b₁) (a₂ , b₂)
  ΣFirst {a₁} {a₂} {b₁} {b₂} eq = ∧right (Σorder {a₁ = a₁} {a₂} {b₁} {b₂}) (left eq)

  ΣSecond : {a : A} {b₁ b₂ : B a} → b₁ << b₂ → ord (Σ A B) (a , b₁) (a , b₂)
  ΣSecond {a} {b₁} {b₂} eq = ∧right (Σorder {a₁ = a} {a} {b₁} {b₂}) (right (refl , eq))

  leftΣSucc : A → Succ (Σ A B)
  leftΣSucc a = {!!}

  isInf : (a : Succ A) (x : Succ (Σ A B)) → Set
  isInf a x = (a₁ : A) (b : B a₁) → left a₁ << a → left (a₁ , b) << x

  isInfFirst : (a a' : A) (b : B a')→ isInf (left a) (left (a' , b)) → a ≤ a'
  isInfFirst a a' b isinf = ≤Total (λ eq → <<Irefl {A = Succ (Σ A B)} (left (a' , b)) (isinf a' b (inc₀Order {a₁ = a'} {a₂ = a} eq)) )

  ΣSucc : Succ A → Succ (Σ A B)
  ΣSucc (left a) = leftΣSucc a
  ΣSucc (right *) = right *

  ΣSuccInc : (a : A) → Succ (B a) → Succ (Σ A B)
  ΣSuccInc a (left b) = left (a , b)
  ΣSuccInc a (right *) = ΣSucc (inc₁ a)

  ΣSuccInf : (a : Succ A) → isInf a (ΣSucc a)
  ΣSuccInf = {!!}

  ΣSuccInfMin : {a : Succ A} {x : Succ (Σ A B)} → isInf a x → ΣSucc a ≤ x
  ΣSuccInfMin = {!!}

  ΣSuccDef : {a : Succ A} {x : Succ (Σ A B)} → isInf a x → ((y : Succ (Σ A B)) → isInf a y → x ≤ y) → x ≡ ΣSucc a 
  ΣSuccDef = {!!}

  ΣSuccOrder : {a₁ a₂ : Succ A} → a₁ ≤ a₂ → ΣSucc a₁ ≤ ΣSucc a₂
  ΣSuccOrder (left refl) = left refl
  ΣSuccOrder (right eq) = {!!} --≤Total (λ eq₂ → {!!})

  ΣSuccIncOrder : {a : A} {b b' : Succ (B a)} → b ≤ b' → ΣSuccInc a b ≤ ΣSuccInc a b'
  ΣSuccIncOrder (left refl) = left refl
  ΣSuccIncOrder {a} {left b} {left b'} (right eq) = right (inc₀Order {A = Σ A B} {a₁ = (a , b)} {a₂ = (a , b')}
                                                                     (ΣSecond (inc₀OrderConverse {a₁ = b} {a₂ = b'} eq)))
  ΣSuccIncOrder {a} {left b} {right *} (right eq) = right (ΣSuccInf (inc₁ a) a b (succIsSucc {a = a}))
  ΣSuccIncOrder {a} {right *} {left b'} (right eq) = <<Total {x = right *} {y = left b'} eq (maxIsMax (left b'))
  ΣSuccIncOrder {a} {right *} {right *} (right eq) = left refl

  ΣSuccIncOrderMinAux₁ : {a a' : A} {b : Succ (B a)} {b' : Succ (B a')} → a << a' → ΣSuccInc a b ≤ ΣSuccInc a' b'
  ΣSuccIncOrderMinAux₁ {a} {a'} {b = left b} {left b'} eq = right (inc₀Order {A = Σ A B} {a₁ = a , b} {a₂ = a' , b'}
                                                                             (ΣFirst eq))
  ΣSuccIncOrderMinAux₁ {a} {a'} {b = left b} {right *} eq = right (ΣSuccInf (inc₁ a') a b (<<Trans {x = left a} {y = left a'} {z = inc₁ a'}
                                                                                                   (inc₀Order {a₁ = a} {a₂ = a'} eq) (succIsSucc {a = a'})))
  ΣSuccIncOrderMinAux₁ {a} {a'} {right *} {left b'} eq = ΣSuccInfMin {a = inc₁ a} {x = left (a' , b')}
                                                                     (λ a₁ b eq₂ → inc₀Order {A = Σ A B} {a₁ = a₁ , b} {a₂ = a' , b'}
                                                                                             (ΣFirst (inc₀OrderConverse {a₁ = a₁} {a₂ = a'}
                                                                                             (≤<Trans {x = inc₀ a₁} {y = inc₀ a} {z = inc₀ a'}
                                                                                                      {!!}
                                                                                                      (inc₀Order {a₁ = a} {a₂ = a'} eq)))))
  ΣSuccIncOrderMinAux₁ {a} {a'} {right *} {right *} eq = ΣSuccOrder {a₁ = inc₁ a} {a₂ = inc₁ a'} (right (inc₁Order {a₁ = a} {a₂ = a'} eq))

  ΣSuccIncOrderMin : {a a' : A} {b' : Succ (B a')} → a ≤ a' → ΣSuccInc a min ≤ ΣSuccInc a' b'
  ΣSuccIncOrderMin {b' = b'} (left refl) = ΣSuccIncOrder (minIsMin b')
  ΣSuccIncOrderMin {b' = b'} (right eq) = ΣSuccIncOrderMinAux₁ {b = min} {b' = b'} eq


{-
  ΣSuccIncOrder : {a : A} → {x y : Succ (B a)} → x ≤ y → ΣSuccInc a x ≤ ΣSuccInc a y
  ΣSuccIncOrder (left refl) = left refl
  ΣSuccIncOrder {x = left b₁} {left b₂} (right eq) = right {!!}
  ΣSuccIncOrder {x = left b} {right *} (right eq) = right {!!}
  ΣSuccIncOrder {x = right *} (right eq) = right {!!}
-}
{-
  ΣSuccIncOrderFirst : {a₁ a₂ : A} → {b₁ : Succ (B a₁)} → {b₂ : Succ (B a₂)} → a₁ << a₂ → ΣSuccInc a₁ b₁ ≤ ΣSuccInc a₂ b₂
  ΣSuccIncOrderFirst {b₁ = left b₁} {left b₂} = {!!}
  ΣSuccIncOrderFirst {a₁ = a₁} {a₂ = a₂} {b₁ = left b₁} {right *} eq = right (ΣSuccInf (inc₁ a₂) a₁ b₁ (<<Trans {x = left a₁} {y = left a₂} {z = inc₁ a₂}
                                                                                                         (inc₀Order {a₁ = a₁} {a₂ = a₂} eq)
                                                                                                         (succIsSucc {a = a₂}))) 
  ΣSuccIncOrderFirst {b₁ = right *} {left x₂} = {!!}
  ΣSuccIncOrderFirst {b₁ = right *} {right x₂} = {!!}
-}

  ΣSuccMin : ΣSucc (min {A}) ≡ min {Σ A B}
  ΣSuccMin = isMinDef λ { (left (a , b)) → ΣSuccInfMin {min {A}} (λ a₁ b₁ eq → <<Total eq (minIsMin (left a₁))) ;
                          (right *) → maxIsMax (ΣSucc min)}


  ΣSuccIncMinAux : {a a' : A} {b : B a} {b' : Succ (B a')} → a << a' → left (a , b) << ΣSuccInc a' b'
  ΣSuccIncMinAux {a} {a'} {b} {left b'} eq = inc₀Order {A = Σ A B} {a₁ = (a , b)} {a₂ = (a' , b')} (ΣFirst eq)
  ΣSuccIncMinAux {a} {a'} {b} {right *} eq = ΣSuccInf (inc₁ a') a _ (<<Trans {x = left a} {y = left a'} {z = inc₁ a'}
                                                                             (inc₀Order {a₁ = a} {a₂ = a'} eq)
                                                                             (succIsSucc {a = a'}))
  

  ΣSuccIncMin : {a : A} → ΣSuccInc a (min {B a}) ≡ ΣSucc (left a)
  ΣSuccIncMin {a} = ΣSuccDef {a = left a} {x = ΣSuccInc a (min {B a})}
                             (λ a₁ b eq → ΣSuccIncMinAux {b' = min} (inc₀OrderConverse {a₁ = a₁} {a₂ = a} eq) )
                             λ { (left (a' , b)) x → ΣSuccIncOrderMin {a = a} {a' = a'} {left b}
                                                                   (isInfFirst a a' b x) ;
                                 (right *) x → maxIsMax _}


  ΣSuccIncInc₁ : {a : A} {b : B a} → inc₁ (a , b) ≡ ΣSuccInc a (inc₁ b)
  ΣSuccIncInc₁ = {!!}


minMorphism : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} (f : A → B) → HomFO f → ∨Nat f Id (min {A}) ≡ min {B}
minMorphism = {!!}


ΣSuccΣFunBase : {A₁ A₂ : Set} {{_ : FOSet A₁}} {{_ : FOSet A₂}}
            {B : A₂ → Set} {{_ : {a₂ : A₂} → FOSet (B a₂)}}
            {f : A₁ → A₂} (homf : HomFO f)
            {a : Succ A₁} → ΣSucc {B = B} (∨Nat f Id a) ≡ ∨Nat (Σfun f Id) Id (ΣSucc {B = B o f} a)
ΣSuccΣFunBase = {!!}

ΣSuccΣFunFibre : {A : Set} {{_ : FOSet A}}
            {B₁ : A → Set} {B₂ : A → Set} {{_ : {a : A} → FOSet (B₁ a)}} {{_ : {a : A} → FOSet (B₂ a)}}
            {F : {a : A} → B₁ a → B₂ a} (HomF : {a : A} → HomFO (F {a}))
            {a : Succ A} → ΣSucc {B = B₂} a ≡ ∨Nat (Σfun Id F) Id (ΣSucc {B = B₁} a)
ΣSuccΣFunFibre = {!!}


module _ {A : Set} {{_ : FOSet A}} {B : A → Set} {{_ : {a : A} → FOSet (B a)}} {C : Σ A B → Set} {{_ : {x : Σ A B} → FOSet (C x)}} where

  ΣSuccψ : (a : Succ A) → ΣSucc (ΣSucc a) ≡ ∨Nat (ψ A B C) Id (ΣSucc a)
  ΣSuccψ (left a) = {!!}
  ΣSuccψ (right *) = refl

  ΣSuccψInc₁ : (a : A) (b : Succ (B a)) → ΣSucc (ΣSuccInc a b) ≡ ∨Nat (ψ A B C) Id (ΣSuccInc a (ΣSucc b))
  ΣSuccψInc₁ a (left b) = {!!}
  ΣSuccψInc₁ a (right *) = ΣSuccψ (inc₁ a)




--We define string of composable paths

record composablePath {k} (X : Set k) (A : Set) {{_ : FOSet A}} : Set k where
  field
    point : Succ A → X
    path : (a : A) → point (inc₀ a) ~~> point (inc₁ a)


module _ {k} {X : Set k} {A : Set} {{_ : FOSet A}} where


  ≡ComposablePathAux2 : {P Q : composablePath X A}
                       → composablePath.point P ≡ composablePath.point Q
                       → ((a : A) (i : I) → composablePath.path P a $ i ≡ composablePath.path Q a $ i)
                       → P ≡ Q
                     
  ≡ComposablePathAux2 {P = record { point = f ; path = F }} {Q = record { point = g ; path = G }} refl eqPath = ap (λ H → record { point = f ; path = H })
                                                                                                 (funext (λ a → ≡Path (eqPath a)))


  ≡ComposablePathAux1 : {P Q : composablePath X A}
                    → ((a : Succ A) → composablePath.point P a ≡ composablePath.point Q a)
                    → ((a : A) (i : I) → composablePath.path P a $ i ≡ composablePath.path Q a $ i)
                    → P ≡ Q
                  
  ≡ComposablePathAux1 eqPoint eqPath = ≡ComposablePathAux2 (funext eqPoint) eqPath


  ≡ComposablePath :  {P Q : composablePath X A}
                     → composablePath.point P max ≡ composablePath.point Q max
                    → ((a : A) (i : I) → composablePath.path P a $ i ≡ composablePath.path Q a $ i)
                    → P ≡ Q

  ≡ComposablePath {P} {Q} eqPoint eqPath = ≡ComposablePathAux1 (λ { (left a) → ≡Trans {y = composablePath.path P a $ e₀}
                                                                              (≡Sym (eqe₀ (composablePath.path P a)))
                                                                              (≡Trans (eqPath a e₀)
                                                                                      (eqe₀ (composablePath.path Q a))) ;
                                                                    (right *) → eqPoint}) eqPath


  firstPoint : composablePath X A → X
  firstPoint p = composablePath.point p min

  lastPoint : composablePath X A → X
  lastPoint p = composablePath.point p max

  composableHrefl : X → composablePath X A
  composableHrefl x = record { point = λ _ → x ; path = λ _ → hrefl }

  loopComposable : {x : X} → (A → x ~~> x) → composablePath X A
  loopComposable {x = x} f = record { point = λ _ → x ; path = f }


module _ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {B : A → Set} {{_ : {a : A} → FOSet (B a)}} where

  ΣComposablePath : (a : A) → composablePath X (Σ A B) → composablePath X (B a)
  ΣComposablePath a record { point = f ; path = F }
                    = record { point = f o ΣSuccInc a ;
                               path = λ b → endpointPath (F (a , b)) refl (ap f ΣSuccIncInc₁) }

  ΣComposablePathHrefl : {a : A} {x : X} → ΣComposablePath a (composableHrefl x) ≡ composableHrefl x
  ΣComposablePathHrefl = ≡ComposablePath refl (λ _ _ → refl)

  

--Now we show functoriality of the strings of composable paths

module _ {k} {X : Set k} where

  composablePathFunct : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}}
                        (f : A → B) → HomFO f → composablePath X B → composablePath X A
                        
  composablePathFunct f homf record { point = g ;
                                      path = G }
                           = record { point = g o ∨Nat f Id ;
                                      path = λ a → endpointPath (G (f a)) refl (ap g (inc₁morphism f homf)) }


  composablePathFunctId : {A : Set} {{_ : FOSet A}} {a : composablePath X A}
                          → composablePathFunct Id HomFOId a ≡ a
                        
  composablePathFunctId {a = record { point = f ; path = F }} = ≡ComposablePath refl (λ _ _ → refl)


  composablePathFunctComp : {A B C : Set} {{_ : FOSet A}} {{_ : FOSet B}} {{_ : FOSet C}}
                            {f : A → B} {g : B → C} (homf : HomFO f) (homg : HomFO g) (c : composablePath X C)
                            → composablePathFunct f homf (composablePathFunct g homg c) ≡ composablePathFunct (g o f) (HomFOComp homf homg) c

  composablePathFunctComp homf homg record { point = h ; path = H } = ≡ComposablePath refl (λ _ _ → refl)

 

module _ {k} {X : Set k} {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}}
         (f : A → B) (homf : HomFO f) where

       composablePathFunctFirstPoint : (p : composablePath X B) → firstPoint (composablePathFunct f homf p) ≡ firstPoint p
       composablePathFunctFirstPoint record { point = g ; path = G } = ap g (minMorphism f homf)

       composablePathFunctLastPoint : (p : composablePath X B) → lastPoint (composablePathFunct f homf p) ≡ lastPoint p
       composablePathFunctLastPoint record { point = g ; path = G } = refl 

       composablePathFunctHrefl : {x : X} → composablePathFunct f homf (composableHrefl x) ≡ composableHrefl x
       composablePathFunctHrefl = ≡ComposablePath refl (λ _ _ → refl)

       loopComposableFunct : {x : X} {a : B → x ~~> x} → composablePathFunct f homf (loopComposable a) ≡ loopComposable (a o f)
       loopComposableFunct {a = a} = ≡ComposablePath refl (λ _ _ → refl)


--We define the path operad

module _ {k} (X : Set k) where

  record PathOp (A : Set) {{_ : FOSet A}} : Set k where
    field
      fun : (p : composablePath X A) → firstPoint p ~~> lastPoint p
      equality : (x : X) → fun (composableHrefl x) ≡ hrefl


≡PathOpAux : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {P Q : PathOp X A}
          → PathOp.fun P ≡ PathOp.fun Q → P ≡ Q
          
≡PathOpAux {P = record { fun = ϕ ; equality = eqϕ }} {record { fun = ψ ; equality = eqψ }} refl = ap (λ H → record { fun = ϕ ; equality = H }) (funext (λ _ → UIP)) 


≡PathOp : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {P Q : PathOp X A}
          → ((p : composablePath X A) → PathOp.fun P p ≡ PathOp.fun Q p) → P ≡ Q
          
≡PathOp equalFun = ≡PathOpAux (funext equalFun)



module _ {k} {X : Set k} where


  PathOpFun : {A B : Set} → {{_ : FOSet A}} → {{_ : FOSet B}}
              → (f : A → B) → HomFO f → PathOp X A → PathOp X B

  PathOpFun f homf record { fun = ϕ ; equality = eq } =
                   record { fun = λ {p → endpointPath  (ϕ (composablePathFunct f homf p))
                                                      (composablePathFunctFirstPoint f homf p)
                                                      (composablePathFunctLastPoint f homf p)}  ;
                            equality = λ x → ≡Path (λ i → ≡Trans {y = ϕ (composableHrefl x) $ i}
                                                                 (ap (λ H → ϕ H $ i) (composablePathFunctHrefl f homf))
                                                                 (ap (λ p → p $ i) (eq x))) }


  PathOpFunCompute :  {A B : Set} → {{_ : FOSet A}} → {{_ : FOSet B}}
              → {f : A → B} → {homf : HomFO f} → (c : PathOp X A) {p : composablePath X B} {i : I}
              → PathOp.fun (PathOpFun f homf c) p $ i ≡ PathOp.fun c (composablePathFunct f homf p) $ i 

  PathOpFunCompute record { fun = ϕ ; equality = eqϕ } = refl
  

  γPathOp : {A : Set} {B : A → Set} {{_ : FOSet A}} {{_ : {a : A} → FOSet (B a)}}
            → PathOp X A → ((a : A) → PathOp X (B a)) → PathOp X (Σ A B)
  γPathOp {A = A} {B = B} ( record { fun = ϕ ; equality = eqϕ }) d =
                  record { fun = λ {record { point = f ; path = F }
                                    → endpointPath (ϕ (record { point = f o ΣSucc ;
                                                                           path = λ a → endpointPath (PathOp.fun (d a)
                                                                                        (ΣComposablePath a (record { point = f ; path = F })))
                                                                                        (ap f ΣSuccIncMin) refl } ))
                                      (ap (λ a → f a) ΣSuccMin) refl };
                                                        
                              equality = λ x → ≡Trans {y = ϕ (composableHrefl x)}
                                                      (≡Path (λ i → ap (λ H → ϕ H $ i)
                                                      (≡ComposablePath refl
                                                                       (λ a i → ≡Trans {y = PathOp.fun (d a) (composableHrefl x) $ i}
                                                                                       (ap (λ H → PathOp.fun (d a) H $ i) (ΣComposablePathHrefl {B = B}))
                                                                                       (ap (λ H → H $ i) (PathOp.equality (d a) x))))))
                                                      (eqϕ x) }


  γPathOpCompute : {A : Set} {B : A → Set} {{_ : FOSet A}} {{_ : {a : A} → FOSet (B a)}}
                   (c : PathOp X A) (d : (a : A) → PathOp X (B a))
                   {f : Succ (Σ A B) → X} {F : (x : Σ A B) → f (inc₀ x) ~~> f (inc₁ x)} {i : I}
                   → PathOp.fun (γPathOp c d) (record {point = f ; path = F}) $ i
                     ≡ (PathOp.fun c (record { point = f o ΣSucc ; path = λ a → endpointPath (PathOp.fun (d a) (ΣComposablePath a (record { point = f ; path = F })))
                                                                                                        (ap f ΣSuccIncMin) refl }) $ i)

  γPathOpCompute record { fun = ϕ ; equality = eqϕ } d = refl



  idPathOp : PathOp X (Fin (s O))
  idPathOp = record { fun = λ p → composablePath.path p fzero ;
                      equality = λ _ → refl }


{-
  UnitLeftPathOp : {A : Set} ⦃ _ : FOSet A ⦄ (c : PathOp X A) →
                   γPathOp c (λ _ → idPathOp) ≡ PathOpFun (η₂ _) HomFOη₂ c

  UnitLeftPathOp (record { fun = ϕ ; equality = eqϕ }) = ≡PathOp (λ { record { point = f ; path = F }
                                                       → ≡Path (λ i → ap (λ H → ϕ H $ i)
                                                                         (≡ComposablePath refl (λ _ _ → refl)))})


  UnitRightPathOp : {B : Fin (s O) → Set} ⦃ _ : {x : Fin (s O)} → FOSet (B x) ⦄
                    (d : (x : Fin (s O)) → PathOp X (B x)) →
                    γPathOp idPathOp d ≡ PathOpFun (η₁ B) HomFOη₁ (d fzero)

  UnitRightPathOp d = ≡PathOp (λ { record { point = f ; path = F }
                              → ≡Path (λ i → ≡Trans (ap (λ H → PathOp.fun (d fzero) H $ i) (≡ComposablePath refl (λ _ _ → refl)))
                                                    (≡Sym (PathOpFunCompute (d fzero))) ) } )


  NaturalityFiberPathOp : {A : Set} ⦃ _ : FOSet A ⦄ {B₁ B₂ : A → Set} ⦃ _ : {a : A} → FOSet (B₁ a) ⦄ ⦃ _ : {a : A} → FOSet (B₂ a) ⦄
                          (F : {a : A} → B₁ a → B₂ a) (homF : {a : A} → HomFO F)
                          (c : PathOp X A) (d : (a : A) → PathOp X (B₁ a))
                          → PathOpFun (Σfun Id F) (HomFOΣfun HomFOId homF) (γPathOp c d) ≡ γPathOp c (λ a → PathOpFun (F {a}) (homF {a}) (d a))

  NaturalityFiberPathOp F homF record { fun = ϕ ; equality = eqϕ } d = ≡PathOp (λ { record { point = g ; path = G }
                                                                     → ≡Path (λ i → ap (λ H → ϕ H $ i)
                                                                     (≡ComposablePath refl
                                                                     (λ a j → ≡Trans (ap (λ H → PathOp.fun (d a) H $ j)
                                                                                     (≡ComposablePath (ap g (≡Sym (ΣSuccΣFunFibre homF {a = inc₁ a})))
                                                                                                      λ _ _ → refl))
                                                                                     (≡Sym (PathOpFunCompute (d a))))))})



  NaturalityBasePathOp : {A₁ A₂ : Set} ⦃ _ : FOSet A₁ ⦄ ⦃ _ : FOSet A₂ ⦄ {B : A₂ → Set} ⦃ _ : {a₂ : A₂} → FOSet (B a₂) ⦄
                         (f : A₁ → A₂) (homf : HomFO f)
                         (c : PathOp X A₁) (d : (a₂ : A₂) → PathOp X (B a₂))
                         → PathOpFun (Σfun f Id) (HomFOΣfun homf HomFOId) (γPathOp c (d o f)) ≡ γPathOp (PathOpFun f homf c) d

  NaturalityBasePathOp f homf record { fun = ϕ ; equality = eqϕ } d =
                         ≡PathOp (λ { record { point = g ; path = G }
                                 → ≡Path (λ i → ap (λ H → ϕ H $ i)
                                         (≡ComposablePath refl (λ a j → ap (λ H → PathOp.fun (d (f a)) H $ j)
                                                                           (≡ComposablePath (ap g (≡Trans (≡Sym (ΣSuccΣFunBase homf {a = inc₁ a}))
                                                                                                          (≡Sym (ap ΣSucc (inc₁morphism f homf {a})))))
                                                                                            (λ _ _ → refl)))))})





  AssocPathOp : {A : Set} {{Afinite : FOSet A}} {B : A → Set}
                {{Bfinite : {a : A} → FOSet (B a)}} {C : Σ A B → Set}
                {{Cfinite : {x : Σ A B} → FOSet (C x)}} (c : PathOp X A {{Afinite}})
                (d : (a : A) → PathOp X (B a) {{Bfinite}}) (e : (x : Σ A B) → PathOp X (C x) {{Cfinite}}) →
                γPathOp {{FOΣ {{Afinite}} {{Bfinite}}}} {{Cfinite}} (γPathOp {{Afinite}} {{Bfinite}} c d) e ≡
                PathOpFun {{FOΣ {{Afinite}} {{FOΣ {{Bfinite}} {{Cfinite}}}}}} {{FOΣ {{FOΣ {{Afinite}} {{Bfinite}}}} {{Cfinite}}}}
                          (ψ A {{Afinite}} B {{Bfinite}} C {{Cfinite}}) (HomFOψ {{Afinite}} {{Bfinite}} {{Cfinite}})
                          (γPathOp {{Afinite}} {{FOΣ {{Bfinite}} {{Cfinite}}}} c (λ a → γPathOp {{Bfinite}} {{Cfinite}} (d a) (λ b → e (a , b))))

  AssocPathOp record { fun = ϕ ; equality = eqϕ } d e =
              ≡PathOp (λ { record { point = g ; path = G }
                      → ≡Path (λ i → ap (λ H → ϕ H $ i)
                                        (≡ComposablePath refl
                                        (λ a j → ≡Trans (ap (λ H → PathOp.fun (d a) H $ j)
                                                            (≡ComposablePath (ap g (ΣSuccψ (inc₁ a)))
                                                                             (λ b k → ap (λ H → PathOp.fun (e (a , b)) H $ k)
                                                                                         (≡ComposablePath (ap g (≡Trans {y = ΣSucc (ΣSuccInc a (inc₁ b))}
                                                                                                                        (ap ΣSucc ΣSuccIncInc₁)
                                                                                                                        (ΣSuccψInc₁ a (inc₁ b))))
                                                                                                          (λ _ _ → refl)))))
                                                        (≡Sym (γPathOpCompute (d a) (λ b → e (a , b)))))))})



  instance
    OperadPathOp : Operad (PathOp X)
    
    OperadPathOp = record
                     { functor = PathOpFun
                     
                     ; functorId = λ { record { fun = ϕ ; equality = _ }
                                       → ≡PathOp λ p → ≡Path (λ i → ap (λ H → ϕ H $ i) composablePathFunctId)}
                     
                     ; functorComp = λ { {homf = homf} {homg = homg} record { fun = ϕ ; equality = _ }
                                         → ≡PathOp (λ p → ≡Path (λ i → ap (λ H → ϕ H $ i) (composablePathFunctComp homf homg p)))}
                     
                     ; id = idPathOp
                     
                     ; γ = γPathOp
                     
                     ; unitLeft = UnitLeftPathOp 
                     
                     ; unitRight = UnitRightPathOp 
                     
                     ; naturalityFiber = NaturalityFiberPathOp
                     
                     ; naturalityBase = NaturalityBasePathOp
                     
                     ; assoc = AssocPathOp
                     }




--We define the morphisms from the path operad to the endomorphism operads


  PathOpToEnd : (x : X) → Nat (PathOp X) (End (x ~~> x))
  
  PathOpToEnd _ _ ϕ p = PathOp.fun ϕ (loopComposable p)
 

  HomPathOpToEnd : (x : X) → HomOperad (PathOpToEnd x)
  
  HomPathOpToEnd x = record { homNat = λ { {f = f} homf {record { fun = ϕ ; equality = eq }}
                                           → funext (λ a → ≡Path (λ i → (ap (λ H → ϕ H $ i) (loopComposableFunct f homf {a = a}))))} ;
                                           
                              homId = refl ;
                              
                              homγ = λ { {A} {B = B} {c = record { fun = ϕ ; equality = eqϕ }} {d}
                                       → funext (λ p → ≡Path (λ i → ap (λ H → ϕ H $ i)
                                                             (≡ComposablePath refl
                                                             (λ a j → ap (λ H → PathOp.fun (d a) H $ j)
                                                                         (≡ComposablePath refl (λ _ _ → refl)))))) }}


-}

--We prove the path operad is strongly contractible


  StronglyContractiblePathOp : {{_ : Fib X}} {A : Set} {{_ : FOSet A}} → StronglyContractible (PathOp X A)
  
  StronglyContractiblePathOp = {!!}



