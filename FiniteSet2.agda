{-# OPTIONS --allow-unsolved-metas #-}

module FiniteSet2 where

open import Data
open import FiniteSet
open import MorphismFiniteSet


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

FinEmpty : ∀ {k} {X : Set k} → Fin O → X
FinEmpty ()




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




--We develop a bit of theory for total order.

<Trans : {n : ℕ} {x y z : Fin n} → x << y → y << z → x << z
<Trans {.(s _)} {fzero} {fzero} {z} ()
<Trans {.(s _)} {fzero} {fsucc y} {fzero} _ () 
<Trans {.(s _)} {fzero} {fsucc y} {fsucc z} _ _ = *
<Trans {.(s _)} {fsucc x} {fzero} {z} () 
<Trans {.(s _)} {fsucc x} {fsucc y} {fzero} _ ()
<Trans {.(s _)} {fsucc x} {fsucc y} {fsucc z} = <Trans {x = x} {y} {z}


module _ {A : Set} {{_ : FOSet A}} where

  <<Trans : {x y z : A} → x << y → y << z → x << z
  <<Trans {x = x} {y} {z} = <Trans {x = funFO x} {y = funFO y} {z = funFO z}

  _≤_ : (a b : A) → Set
  a ≤ b = (a ≡ b) ∨ (a << b)


≤Canonical : {A : Set} {{_ : FOSet A}} {x y : A} → funFO x ≤ funFO y → x ≤ y
≤Canonical (left eq) = left (isoCancel isIsoFO eq)
≤Canonical (right eq) = right eq

fsucc≤ : {n : ℕ} {x y : Fin n} → x ≤ y → fsucc x ≤ fsucc y 
fsucc≤ (left refl) = left refl
fsucc≤ (right eq) = right eq

≤TotalCanonical : {n : ℕ} {x y : Fin n} → ¬ (y << x) → x ≤ y
≤TotalCanonical {x = fzero} {fzero} _ = left refl
≤TotalCanonical {x = fzero} {fsucc y} _ = right *
≤TotalCanonical {x = fsucc x} {fzero} eq = efql (eq *)
≤TotalCanonical {x = fsucc x} {fsucc y} eq = fsucc≤ (≤TotalCanonical eq)

module _ {A : Set} {{_ : FOSet A}} where

  <<Total : ∀ {k} {X : Set k} {x y : A} → x << y → y ≤ x → X
  <<Total {x = x} eq₁ (left refl) = efql (<<Irefl x eq₁)
  <<Total {x = x} {y} eq₁ (right eq₂) = efql (<<Irefl x (<<Trans {x = x} {y = y} {z = x} eq₁ eq₂))

  ≤Total : {x y : A} → ¬ (y << x) → x ≤ y
  ≤Total eq = ≤Canonical (≤TotalCanonical eq)

  ≤AntiSym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  ≤AntiSym (left refl) eq₂ = refl
  ≤AntiSym (right eq₁) eq₂ = <<Total eq₁ eq₂

  ≤<Trans : {x y z : A} → x ≤ y → y << z → x << z
  ≤<Trans (left refl) eq₂ = eq₂
  ≤<Trans {x = x} {y} {z} (right eq₁) eq₂ = <<Trans {x = x} {y} {z} eq₁ eq₂




--Basics for inc₀ and inc₁

inc₀OrderCanonical : {n : ℕ} {k l : Fin n} → k < l →  Fin⊤SuccAux k << Fin⊤SuccAux l
inc₀OrderCanonical {k = fzero} {fzero} = Id
inc₀OrderCanonical {k = fzero} {fsucc l} _ = *
inc₀OrderCanonical {k = fsucc k} {fzero} = Id
inc₀OrderCanonical {k = fsucc k} {fsucc l} x = inc₀OrderCanonical {k = k} {l} x

inc₀OrderConverseCanonical : {n : ℕ} {k l : Fin n} → Fin⊤SuccAux k << Fin⊤SuccAux l → k < l
inc₀OrderConverseCanonical {k = fzero} {fzero} = Id
inc₀OrderConverseCanonical {k = fzero} {fsucc l} _ = *
inc₀OrderConverseCanonical {k = fsucc k} {fzero} = Id
inc₀OrderConverseCanonical {k = fsucc k} {fsucc l} x = inc₀OrderConverseCanonical {k = k} {l} x

inc₀Order : {A : Set} {{_ : FOSet A}} → {a₁ a₂ : A} → a₁ << a₂ → inc₀ a₁ << inc₀ a₂
inc₀Order {a₁ = a₁} {a₂} = inc₀OrderCanonical {k = funFO a₁} {l = funFO a₂}

inc₀Order≤ : {A : Set} {{_ : FOSet A}} → {a₁ a₂ : A} → a₁ ≤ a₂ → inc₀ a₁ ≤ inc₀ a₂
inc₀Order≤ (left refl) = left refl
inc₀Order≤ {a₁ = a₁} {a₂} (right eq) = right (inc₀Order {a₁ = a₁} {a₂ = a₂} eq)

inc₀OrderConverse : {A : Set} {{_ : FOSet A}} → {a₁ a₂ : A} → inc₀ a₁ << inc₀ a₂ →  a₁ << a₂
inc₀OrderConverse {a₁ = a₁} {a₂} = inc₀OrderConverseCanonical {k = funFO a₁} {l = funFO a₂}

≡inc₁ : {A : Set} {{_ : FOSet A}} (a : A) → fsucc (funFO a) ≡ funFO (inc₁ a)
≡inc₁ {A} a = iso.invLeft (isIsoFO {A = Succ A}) (fsucc (funFO a))

inc₁Order : {A : Set} {{_ : FOSet A}} → {a₁ a₂ : A} → a₁ << a₂ → inc₁ a₁ << inc₁ a₂
inc₁Order {A} {a₁} {a₂} eq = transport₂ _<_ (≡inc₁ a₁) (≡inc₁ a₂) eq

succIsSuccCanonical : {n : ℕ} → {x : Fin n} → Fin⊤SuccAux x < fsucc x
succIsSuccCanonical {x = fzero} = *
succIsSuccCanonical {x = fsucc x} = succIsSuccCanonical {x = x}

succIsSucc : {A : Set} {{_ : FOSet A}} → {a : A} → inc₀ a << inc₁ a
succIsSucc {A} {a} = transport (λ k → funFO (inc₀ a) < k) (≡inc₁ a) (succIsSuccCanonical {x = funFO a})

succ≤Canonical : {n : ℕ} {k l : Fin n} → Fin⊤SuccAux k << fsucc l → k ≤ l
succ≤Canonical {k = fzero} {fzero} _ = left refl
succ≤Canonical {k = fzero} {fsucc l} _ = right *
succ≤Canonical {k = fsucc k} {fzero} eq = efql eq
succ≤Canonical {k = fsucc k} {fsucc l} eq = fsucc≤ (succ≤Canonical {k = k} {l = l} eq)

succ≤ : {A : Set} {{_ : FOSet A}} → {a₁ a₂ : A} → inc₀ a₁ << inc₁ a₂ → inc₀ a₁ ≤ inc₀ a₂
succ≤ {a₁ = a₁} {a₂} eq = inc₀Order≤ {a₁ = a₁} {a₂ = a₂}
                                     (≤Canonical (succ≤Canonical {k = funFO a₁} {l = funFO a₂}
                                     (transport (λ x → funFO (inc₀ a₁) < x) {x = funFO (inc₁ a₂)} {y = fsucc (funFO a₂)}
                                                (≡Sym (≡inc₁ a₂)) eq)))

inc₀Order↔ : {A : Set} {{_ : FOSet A}} {a₁ a₂ : A} → a₁ << a₂ ↔ inc₀ a₁ << inc₀ a₂
inc₀Order↔ {a₁ = a₁} {a₂} = inc₀Order {a₁ = a₁} {a₂} , inc₀OrderConverse {a₁ = a₁} {a₂}



--Things about min and max

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

fzeroIsMin : {n  : ℕ} → isMin (fzero {n = n})
fzeroIsMin fzero = left refl
fzeroIsMin (fsucc _) = right *

minIsMin : {A : Set} {{_ : FOSet A}} → isMin (min {A})
minIsMin {A} ⦃ record { cardinal = O ; funFO = f ; isIsoFO = isof } ⦄ = λ { (left x) → FinEmpty (f x) ; (right *) → left refl}
minIsMin {A} ⦃ record { cardinal = s |A| ; funFO = f ; isIsoFO = isof } ⦄ (left x) =
             inc₀Order≤ {A} ⦃ record { cardinal = s |A| ; funFO = f ; isIsoFO = isof } ⦄
               {iso.inv isof fzero} {x} (≤Canonical ⦃ record { cardinal = s |A| ; funFO = f ; isIsoFO = isof } ⦄
                                           {x = iso.inv isof fzero} {y = x} (transport (λ y → y ≤ f x)
                                           (iso.invLeft isof fzero) (fzeroIsMin (f x))))
minIsMin {A} ⦃ record { cardinal = s |A| ; funFO = f ; isIsoFO = isof } ⦄ (right *) =
             maxIsMax ⦃ record { cardinal = s |A| ; funFO = f ; isIsoFO = isof } ⦄  (left (iso.inv isof fzero))

isMinDef : {A : Set} {{_ : FOSet A}} {x : Succ A} → isMin x → x ≡ min {A}
isMinDef minx = ≤AntiSym (minx min) (minIsMin _)



--We show inc₁ is successor of inc₀

isSuccessor : {A : Set} {{_ : FOSet A}} (a b : A) → Set
isSuccessor {A} a b = (a << b) ∧ ((c : A) → a << c → b ≤ c)

Inc₁IsSuccessorCanonical : {n : ℕ} {k : Fin (s n)} {l : Fin n} → Fin⊤SuccAux l << k → fsucc l ≤ k
Inc₁IsSuccessorCanonical {k = fzero} eq = efql eq
Inc₁IsSuccessorCanonical {k = fsucc k} {fzero} _ = fsucc≤ (fzeroIsMin k)
Inc₁IsSuccessorCanonical {k = fsucc k} {fsucc l} eq = fsucc≤ (Inc₁IsSuccessorCanonical {k = k} {l} eq)

Inc₁IsSuccessor : {A : Set} {{_ : FOSet A}} {a : A} → isSuccessor (inc₀ a) (inc₁ a)
Inc₁IsSuccessor {a = a} = succIsSucc {a = a} ,
                          λ c eq → ≤Canonical (transport (λ x → x ≤ funFO c) (≡inc₁ a) (Inc₁IsSuccessorCanonical eq))

successorUnique : {A : Set} {{_ : FOSet A}} {a b c : A} → isSuccessor a b → isSuccessor a c → b ≡ c
successorUnique {b = b} {c} sucb succ = ≤AntiSym (∧right sucb c (∧left succ))
                                                 (∧right succ b (∧left sucb))

Inc₁IsSuccessorDef : {A : Set} {{_ : FOSet A}} {a : A} {x : Succ A} → isSuccessor (inc₀ a) x → x ≡ inc₁ a
Inc₁IsSuccessorDef {A} {a = a} {x} sucx = successorUnique {a = inc₀ a} {b = x} {c = inc₁ a} sucx (Inc₁IsSuccessor {a = a}) 


--Things about naturality of Succ, and morphisms

module _  {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} where

  SuccNat : (A → B) → Succ A → Succ B
  SuccNat f = ∨Nat f Id

  HomFOSucc : {f : A → B} → HomFO f → HomFO (SuccNat f)
  HomFOSucc {f} record { isoHomFO = isof ;
                         orderPreserving = ordf }
          = record { isoHomFO = iso∨Nat isof isoId ;
                     orderPreserving = λ { (left x₂) (left x₃) → ↔Trans _ (↔Sym (inc₀Order↔ {a₁ = x₂} {a₂ = x₃}))
                                                                          (↔Trans _ (ordf x₂ x₃)
                                                                                    (inc₀Order↔ {a₁ = f x₂} {a₂ = f x₃})) ;
                                           (left x₂) (right *) → (λ _ → fmaxIsMax {x = funFO (f x₂)}) , λ _ → fmaxIsMax {x = funFO (x₂)} ;
                                           (right *) (left x₃) → (λ x → <<Total {x = right *} {y = left x₃} x (maxIsMax (left x₃))) ,
                                                                 (λ x → <<Total {x = right *} {y = left (f x₃)} x (maxIsMax (left (f x₃)))) ;
                                           (right *) (right *) → (λ x → efql (<<Irefl {A = Succ A} (right *) x)) ,
                                                                 (λ x → efql (<<Irefl {A = Succ B} (right *) x))  }}


--we show morphism preserve minimum

module _  {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} {f : A → B} (homf : HomFO f) where

  HomFOInv : HomFO (iso.inv (HomFO.isoHomFO homf))
  HomFOInv = record { isoHomFO = isoInv (HomFO.isoHomFO homf) ;
                      orderPreserving = λ x y → ↔Trans (f (iso.inv (HomFO.isoHomFO homf) x) << f (iso.inv (HomFO.isoHomFO homf) y))
                                                       (transport₂↔ _<<_ {a₁ = x} {f (iso.inv (HomFO.isoHomFO homf) x)}
                                                          {y} {f (iso.inv (HomFO.isoHomFO homf) y)} (iso.invLeft (HomFO.isoHomFO homf) x)
                                                                                                    (iso.invLeft (HomFO.isoHomFO homf) y))
                                                       (↔Sym (HomFO.orderPreserving homf _ _)) }

  morph<Converse : {x y : B} →  iso.inv (HomFO.isoHomFO homf) x << iso.inv (HomFO.isoHomFO homf) y → x << y
  morph<Converse {x} {y} = ∧right (HomFO.orderPreserving HomFOInv x y)

  morph≤Converse : {x y : B} → iso.inv (HomFO.isoHomFO homf) x ≤ iso.inv (HomFO.isoHomFO homf) y → x ≤ y
  morph≤Converse (left eq) = left (isoCancel (isoInv (HomFO.isoHomFO homf)) eq)
  morph≤Converse {x} {y} (right eq) = right (morph<Converse eq)


minMorphismAux : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}}
                 (f : A → B) → HomFO f
                 → {x : A} → isMin x → isMin (f x)
                 
minMorphismAux f homf {x} minx b = morph≤Converse homf (transport (λ x₁ → x₁ ≤ iso.inv (HomFO.isoHomFO homf) b)
                                                                  (iso.invRight (HomFO.isoHomFO homf) x)
                                                                  (minx (iso.inv (HomFO.isoHomFO homf) b)))


minMorphism : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} (f : A → B) → HomFO f → SuccNat f (min {A}) ≡ min {B}
minMorphism f homf = isMinDef (minMorphismAux (SuccNat f) (HomFOSucc homf) minIsMin)


successorMorphism : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} (f : A → B) → HomFO f → {x y : A} → isSuccessor x y → isSuccessor (f x) (f y)

successorMorphism f record { isoHomFO = record { inv = g ;
                                                 invLeft = invlg ;
                                                 invRight = invrg } ;
                             orderPreserving = ordf } {x} {y} (eq , ineq)
                  = let homf = record { isoHomFO = record { inv = g ;
                                                 invLeft = invlg ;
                                                 invRight = invrg } ;
                             orderPreserving = ordf } in
                    (∧left (ordf x y) eq) ,
                    λ b eq → morph≤Converse homf (transport (λ x₁ → x₁ ≤ g b) {x = y} {y = g (f y)}
                                                            (invrg y) (ineq (g b) (∧right (ordf x (g b))
                                                            (transport (λ u → f x << u) {x = b} {y = f (g b)}
                                                                       (invlg b) eq))))


module _ {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} (f : A → B) (homf : HomFO f) where

  inc₁morphism : {a : A} → inc₁ (f a) ≡ ∨Nat f Id (inc₁ a)
  inc₁morphism {a} = ≡Sym (Inc₁IsSuccessorDef (successorMorphism (SuccNat f) (HomFOSucc homf)
                                                                 {x = inc₀ a} {y = inc₁ a} (Inc₁IsSuccessor {a = a}) ))



--In this module we examine ΣSucc


module _ {A : Set} {B : A → Set} {{_ : FOSet A}} {{_ : {a : A} → FOSet (B a)}} where

--first preliminary

  ΣFirst : {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} → a₁ << a₂ → ord (Σ A B) (a₁ , b₁) (a₂ , b₂)
  ΣFirst {a₁} {a₂} {b₁} {b₂} eq = ∧right (Σorder {a₁ = a₁} {a₂} {b₁} {b₂}) (left eq)

  ΣSecond : {a : A} {b₁ b₂ : B a} → b₁ << b₂ → ord (Σ A B) (a , b₁) (a , b₂)
  ΣSecond {a} {b₁} {b₂} eq = ∧right (Σorder {a₁ = a} {a} {b₁} {b₂}) (right (refl , eq))


--Here the main definition of ΣSucc

  leftΣSucc : A → Succ (Σ A B)
  leftΣSucc a = {!!}

  isInf : (a : Succ A) (x : Succ (Σ A B)) → Set
  isInf a x = (a₁ : A) (b : B a₁) → left a₁ << a → left (a₁ , b) << x

  isInfFirst : (a a' : A) (b : B a')→ isInf (left a) (left (a' , b)) → a ≤ a'
  isInfFirst a a' b isinf = ≤Total (λ eq → <<Irefl {A = Succ (Σ A B)} (left (a' , b)) (isinf a' b (inc₀Order {a₁ = a'} {a₂ = a} eq)) )

  ΣSucc : Succ A → Succ (Σ A B)
  ΣSucc (left a) = leftΣSucc a
  ΣSucc (right *) = right *

  ΣSuccInf : (a : Succ A) → isInf a (ΣSucc a)
  ΣSuccInf = {!!}

  ΣSuccInfMin : {a : Succ A} {x : Succ (Σ A B)} → isInf a x → ΣSucc a ≤ x
  ΣSuccInfMin = {!!}

  ΣSuccDef : {a : Succ A} {x : Succ (Σ A B)} → isInf a x → ((y : Succ (Σ A B)) → isInf a y → x ≤ y) → x ≡ ΣSucc a 
  ΣSuccDef {a} {x} infx mininfx = ≤AntiSym (mininfx (ΣSucc a) (ΣSuccInf a))
                                           (ΣSuccInfMin {a} {x} infx)


--We define ΣSuccInc

  ΣSuccInc : (a : A) → Succ (B a) → Succ (Σ A B)
  ΣSuccInc a (left b) = left (a , b)
  ΣSuccInc a (right *) = ΣSucc (inc₁ a)


--Now the properties of ΣSucc and ΣSuccInc

  ΣSuccOrder : {a₁ a₂ : Succ A} → a₁ ≤ a₂ → ΣSucc a₁ ≤ ΣSucc a₂
  ΣSuccOrder (left refl) = left refl
  ΣSuccOrder {a₁} {a₂} (right eq) = ΣSuccInfMin {a₁} {ΣSucc a₂}
                                                (λ a₃ b eq₂ → ΣSuccInf a₂ a₃ b
                                                              (<<Trans {x = left a₃} {y = a₁} {z = a₂} eq₂ eq))

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
                                                                                                      (succ≤  {a₁ = a₁} {a} eq₂)
                                                                                                      (inc₀Order {a₁ = a} {a₂ = a'} eq)))))
  ΣSuccIncOrderMinAux₁ {a} {a'} {right *} {right *} eq = ΣSuccOrder {a₁ = inc₁ a} {a₂ = inc₁ a'} (right (inc₁Order {a₁ = a} {a₂ = a'} eq))

  ΣSuccIncOrderMin : {a a' : A} {b' : Succ (B a')} → a ≤ a' → ΣSuccInc a min ≤ ΣSuccInc a' b'
  ΣSuccIncOrderMin {b' = b'} (left refl) = ΣSuccIncOrder (minIsMin b')
  ΣSuccIncOrderMin {b' = b'} (right eq) = ΣSuccIncOrderMinAux₁ {b = min} {b' = b'} eq

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




--We examine the interaction of ΣSucc with morphisms

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

