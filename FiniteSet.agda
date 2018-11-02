module FiniteSet where

--Module containing basic definitions
open import Data




--We define canonical finite sets, together with their total order


--Intuitively fzero is 0, and fsucc n t is the successor of t.

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (s n)
  fsucc : {n : ℕ} → Fin n → Fin (s n)

_<_ : {n : ℕ} → Fin n → Fin n → Set
t < fzero {n} = ⊥
fzero {n} < fsucc {n} t = ⊤
fsucc {n} t₁ < fsucc {n} t₂ = t₁ < t₂





--We define (small) finite totally ordered sets as instance classes

record FOSet (A : Set) : Set where
  field
    cardinal : ℕ
    funFO : A → Fin cardinal
    isIsoFO : iso funFO  

open FOSet {{...}} public

_<<_ : {A : Set} {{Afinite : FOSet A}} → A → A → Set
_<<_ {A} {{Afinite}} x y = funFO x < funFO y

infix 56 _<<_


--A few first properties about the order

≡order : {A : Set} {{Afinite : FOSet A}} {x₁ y₁ x₂ y₂ : A} → x₁ ≡ x₂ → y₁ ≡ y₂ → x₁ << y₁ → x₂ << y₂
≡order refl refl q = q







--Prove finiteness of canonical finite sets
instance
  canonicalFOSet : {n : ℕ} → FOSet (Fin n)
  canonicalFOSet {n} = record { cardinal = n ; funFO = Id ; isIsoFO = isoId }



--Some arithmetic with canonical finite sets 

finiteSum : {n : ℕ} (f : Fin n → ℕ) → ℕ
finiteSum {O} _ = O
finiteSum {s n} f = f (fzero) + finiteSum (f o fsucc)


module ArithmeticForCanonicalSets where

  Fin⊥ : ∀ {k} {A : Set k} → Fin O → A
  Fin⊥ ()


--First we define the function Σ Fin Fin → Fin

  Fin+Left : {m n : ℕ} → Fin m → Fin (m + n)
  Fin+Left fzero = fzero
  Fin+Left (fsucc a) = fsucc (Fin+Left a)
  
  --Not sure this is a good def
  Fin+Right : {m n : ℕ} → Fin n → Fin (m + n)
  Fin+Right {O} = Id
  Fin+Right {s m} = fsucc o Fin+Right

  --The function showing canonical finite unions of canonical finite sets finite
  canonicalΣ : {n : ℕ} (S : Fin n → ℕ) → Σ (Fin n) (λ x → Fin (S x)) → Fin (finiteSum S)
  canonicalΣ S (fzero , b) = Fin+Left b
  canonicalΣ S (fsucc a , b) = Fin+Right (canonicalΣ (S o fsucc) (a , b))



--Here we show that it is an isomorphism
--Note that we use extFun in equalCanonicalΣ, so the inverse might not behave well
--Our strategy is to express canonicalΣ as a composition f o (Id ∨ CanonicalΣ) o g in the inductive case, with f and g iso

  --Playing the role of g
  functionAux : {n : ℕ} (S : Fin (s n) → ℕ) → Σ (Fin(s n)) (Fin o S) → Fin (S fzero) ∨ Σ (Fin n) (Fin o S o fsucc)
  functionAux S (fzero , b) = left b
  functionAux S (fsucc a , b) = right (a , b)

  isoFunctionAux : {n : ℕ} (S : Fin (s n) → ℕ) → iso (functionAux S)
  isoFunctionAux S = record { inv = λ { (left b) → fzero , b ; (right (a , b)) → fsucc a , b} ; 
                              invLeft = λ { (left x) → refl ; (right (a , b)) → refl} ; 
                              invRight = λ { (fzero , b) → refl ; (fsucc a , b) → refl} }

  --We probably need to change Fin+Right
  isoFin+LeftRight : {m n : ℕ} → iso {A = Fin m ∨ Fin n} {B = Fin (m + n)} (∨Elim Fin+Left Fin+Right)
  isoFin+LeftRight {O} = {!!} 
  isoFin+LeftRight {s m} = {!!}


  equalCanonicalΣ : {n : ℕ} (S : Fin (s n) → ℕ) → ((∨Elim Fin+Left Fin+Right)  o (∨Nat Id (canonicalΣ (S o fsucc))) o (functionAux S)) ≡ canonicalΣ S
  equalCanonicalΣ S = extFun (λ { (fzero , b) → refl ; (fsucc a , b) → refl})



  isIsoCanonicalΣ : {n : ℕ} (S : Fin n → ℕ) → iso (canonicalΣ S)

  isIsoCanonicalΣ {O} S = record { inv = λ a → Fin⊥ a ; 
                                   invLeft = λ a → Fin⊥ a ; 
                                   invRight = λ {(a , _) → Fin⊥ a} }

  isIsoCanonicalΣ {s n} S = transport iso (equalCanonicalΣ S) 
                     (isoComp {f = (∨Nat Id (canonicalΣ (S o fsucc)) o functionAux S)} {g = ∨Elim Fin+Left Fin+Right} 
                        (isoComp {f = functionAux S} {g = ∨Nat (λ x → x) (canonicalΣ (S o fsucc))} 
                           (isoFunctionAux S) 
                           (iso∨ isoId (isIsoCanonicalΣ (S o fsucc)))) 
                           isoFin+LeftRight) 






--Now prove the order is the one we expect
  Fin+LeftOrder : {m n : ℕ} → (b₁ b₂ : Fin m) 
                  → Fin+Left {n = n} b₁ << Fin+Left {n = n} b₂ ↔ b₁ << b₂
  Fin+LeftOrder fzero fzero = ↔Refl
  Fin+LeftOrder fzero (fsucc b₂) = (λ _ → *) , λ _ → *
  Fin+LeftOrder (fsucc b₁) fzero = (λ ()) , (λ ())
  Fin+LeftOrder {m = s m} {n = n} (fsucc b₁) (fsucc b₂) = Fin+LeftOrder b₁ b₂


  canonicalΣorder : {n : ℕ} (S : Fin n → ℕ) {a₁ a₂ : Fin n} {b₁ : Fin (S a₁)} {b₂ : Fin (S a₂)} 
                    → (canonicalΣ S (a₁ , b₁) < canonicalΣ S (a₂ , b₂)) ↔ ((a₁ < a₂) ∨ Σ (a₁ ≡ a₂) (λ p → transport Fin (ap S p) b₁ < b₂ ))

  canonicalΣorder S {fzero} {fzero} {b₁} {b₂} = ↔Trans (b₁ < b₂) 
                                                       (Fin+LeftOrder b₁ b₂)  
                                                       ((λ q → right (refl , q)) , λ { (left ()) ; (right (refl , q)) → q})

  canonicalΣorder S {fzero} {fsucc a₂} = {!!}

  canonicalΣorder S {fsucc a₁} {a₂} = {!!}





--We only need three results from the module
open ArithmeticForCanonicalSets using (canonicalΣ; isIsoCanonicalΣ; canonicalΣorder) 





--We show that a finite union of finite sets is finite

Σcardinal : (A : Set) {{Afinite : FOSet A}} (B : A → Set) {{Bfinite : {a : A} → FOSet (B a)}} → Fin (cardinal {A}) → ℕ
Σcardinal A ⦃ record { cardinal = |A| ; 
                          funFO = f ; 
                          isIsoFO = record { inv = g ; 
                                             invLeft = invLeft ; 
                                             invRight = invRight } } ⦄ B 
                 = λ n → cardinal {B (g n)}


Σfibre : (A : Set) {{Afinite : FOSet A}} (B : A → Set) {{Bfinite : {a : A} → FOSet (B a)}} → {a : A} → B a → Fin (Σcardinal A B (funFO a))
Σfibre A ⦃ record { cardinal = |A| ; 
                    funFO = f ; 
                    isIsoFO = record { inv = g ; invLeft = invLeft ; invRight = invRight } } ⦄ B {a = a} 
               = λ b → transport (λ a → Fin (cardinal {B a})) (invRight a) (funFO {B a} b)


instance 
  finiteΣ : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} → FOSet (Σ A B)

  finiteΣ {A} {{Afinite}} {B} {{Bfinite}} 
              = let S = Σcardinal A B in let F = Σfibre A B in
                   record { cardinal = finiteSum (Σcardinal A B) ; 
                            funFO = (canonicalΣ S) o (Σfun {B₁ = B} {B₂ = λ n → Fin (S n)} funFO F) ;
                            isIsoFO = isoComp 
                                      (isoΣfun (isIsoFO)
                                      λ a → isoComp (isIsoFO {B a}) (isoTransport (λ a → Fin (cardinal {B a})) (iso.invRight (isIsoFO {A}) a))) 
                                      (isIsoCanonicalΣ S) }
                 




--We give an explicit description of the order on Σ types

transportOrder : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}}
                 {a₁ a₂ : A} (p : a₁ ≡ a₂) {b₁ b₂ : B a₁}
                 → b₁ << b₂ ↔ transport B p b₁ << transport B p b₂

transportOrder refl = ↔Refl


ΣfibreOrder : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} 
              {a : A} {b₁ b₂ : B a} 
              → b₁ << b₂ ↔ Σfibre A B b₁ << Σfibre A B b₂

ΣfibreOrder {A} {B} {a} = let Aux = transportOrder {B = λ a₁ → Fin (cardinal {B a₁})} (iso.invRight (isIsoFO {A}) a) 
                          in (∧left Aux , ∧right Aux)


Σorder : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} 
         → {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}  
         → (a₁ , b₁) << (a₂ , b₂) ↔ (a₁ << a₂ ∨ Σ (a₁ ≡ a₂) (λ p → transport B p b₁ << b₂))

Σorder {A} {{Afinite}} {B} ⦃ Bfinite ⦄ {a₁} {a₂} {b₁} {b₂} 
       = let S = Σcardinal A B in 
         let F = Σfibre A B in 
         let f : A → Fin (cardinal {A})
             f = funFO
         in
         ↔Trans ((f a₁ < f a₂) ∨ (Σ (f a₁ ≡ f a₂) (λ p → transport Fin (ap S p) (F b₁) < F b₂)))
           (canonicalΣorder S {a₁ = f a₁} {a₂ = f a₂} {b₁ = F b₁} {b₂ = F b₂}) 
             (∨Nat↔ ↔Refl (let C = λ p → transport Fin (ap (Σcardinal A B) p) (Σfibre A B b₁) < Σfibre A B b₂ in
                               let u₁ : Σ (f a₁ ≡ f a₂) C → Σ (a₁ ≡ a₂) (C o (ap f))
                                   u₁ = iso.inv (isoΣfun {B₂ = C} {f = (ap f)} 
                                                        {F = Id} (isoAp isIsoFO) (λ _ → isoId)) 
                               in ((λ {(refl , q) → refl , ∧right (ΣfibreOrder {A = A} {b₁ = b₁}) q}) o u₁) ,
                              (λ {(refl , q) → refl ,  ∧left (ΣfibreOrder {A = A} {b₁ = b₁}) q }))) 







--Morphisms between FOSet

record HomFO {A B : Set} {{Afinite : FOSet A}} {{Bfinite : FOSet B}} (f : A → B) : Set where
  field
    isIsoFO : iso f
    orderPreserving : {x y : A} → x << y ↔ f x << f y

open HomFO {{...}} public


{-

--We construct the examples of morphisms  we need for the definition of operads

η₁ : (B : Fin (s O) → Set) {{Bfinite : {x : Fin (s O)} → FOSet (B x)}} → B(fzero O) → Σ (Fin (s O)) B
η₁ B = λ x → (fzero O) , x 

instance
  HomFOId : {A : Set} {{Afinite : FOSet A}} → HomFO (λ (x : A) → x)
  HomFOId = record { isIsoFO = isoId ; orderPreserving = (λ p → p) , (λ q → q) }

  HomFOη₁ : {B : Fin (s O) → Set} {{Bfinite : {x : Fin (s O)} → FOSet (B x)}} → HomFO (η₁ B)
  HomFOη₁ {B} = record { isIsoFO = record { inv = λ {(x , b) → transport B (Fin⊤ x) b} ; 
                                            invLeft = λ { (fzero .O , b) → refl ; (fsucc .O x , b) → efql (Fin⊥ x)} ; 
                                            invRight = λ x → refl } ; 
                         orderPreserving =  {!!} } 

  --HomFOη₂ : {A : Set} {{Afinite : FOSet A}} → HomFO 


-}