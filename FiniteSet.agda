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



{-
--We try another way
  Fin⊥ : ∀ {k} {A : Set k} → Fin O → A
  Fin⊥ () 

  FinS : {n : ℕ} → Fin (s n) → Fin (s O) ∨ Fin (n)
  FinS fzero = left fzero
  FinS (fsucc x) = right x

  isoFinS : {n : ℕ} → iso (FinS {n})
  isoFinS {n} = record { inv = λ { (left _) → fzero ; (right x) → fsucc x} ; 
                     invLeft = λ { (left fzero) → refl ; (right x) → refl} ; 
                     invRight = λ { fzero → refl ; (fsucc a) → refl} }

  Fin⊤Inv : {n : ℕ} → Fin (s O) ∨ Fin (n) → Fin (s n)
  Fin⊤Inv = iso.inv (isoFinS)

  FinSum : {m n : ℕ} → Fin m ∨ Fin n → Fin (m + n)
  FinSum {O} = λ { (left x) → Fin⊥ x ; (right x) → x}
  FinSum {s m} = {!!}
-}

{-

 
  Fin⊥ : ∀ {k} {A : Set k} → Fin O → A
  Fin⊥ ()

  Fin⊤ : (x : Fin (s O)) → x ≡ fzero
  Fin⊤ (fzero) = refl
  Fin⊤ (fsucc x) = (Fin⊥ x)

  FinSucc : {m : ℕ} → Fin(s m) ≅ ⊤ ∨ Fin m
  FinSucc {m} = record { isoFun = λ { (fzero) → left * ; (fsucc x) → right x} ; 
                         isIso = record { inv = λ { (left x) → fzero ; (right x) → fsucc x} ; 
                                    invLeft = λ { (left *) → refl ; (right x) → refl} ; 
                                    invRight = λ { fzero → refl ; (fsucc x) → refl} } }

  Fin+ : {m n : ℕ} → Fin (m + n) ≅ Fin m ∨ Fin n
  Fin+ {O} {n} = iso∨⊥left Fin⊥
  Fin+ {s m} {n} = ≅Trans (⊤ ∨ Fin (m + n)) FinSucc 
                 (≅Trans (⊤ ∨ (Fin m ∨ Fin n)) (iso∨ ≅Refl (Fin+ {m})) 
                 (≅Trans ((⊤ ∨ Fin m) ∨ Fin n) ∨Assoc (iso∨ (≅Sym FinSucc) ≅Refl)))

  isoCanonicalΣAux : {n : ℕ} (f : Fin (s n) → ℕ) 
                 → (Fin (f fzero) ∨ Σ (Fin n) (λ a → Fin (f (fsucc a)))) 
                 ≅ Σ (Fin (s n)) (λ x → Fin (f x))
  isoCanonicalΣAux {n} f = record { isoFun = λ { (left x) → fzero , x ; (right (k , x)) → (fsucc k) , x} ; 
                              isIso = record { inv = λ { (fzero , x) → left x ; (fsucc k , x) → right (k , x)} ; 
                                               invLeft = λ { (fzero , x) → refl ; (fsucc k , x) → refl} ; 
                                               invRight = λ { (left x) → refl ; (right (k , x)) → refl} } }

  isoCanonicalΣ : {n : ℕ} (f : Fin n → ℕ) → Fin (finiteSum f) ≅ Σ (Fin n) (λ x → Fin (f x))
  isoCanonicalΣ {O} _ = iso⊥ Fin⊥ (λ { (a , _) → Fin⊥ a}) 
  isoCanonicalΣ {s n} f = ≅Trans (Fin (f fzero) ∨ Fin (finiteSum (f o fsucc))) 
                        Fin+ (≅Trans (Fin (f fzero) ∨ Σ (Fin n) (Fin o (f o fsucc)))
                               (iso∨ ≅Refl (isoCanonicalΣ (f o fsucc)))
                               (isoCanonicalΣAux f))

  --It is slightly akward that we defined the isomorphism the other way
  canonicalΣ : {n : ℕ} (S : Fin n → ℕ) → Σ (Fin n) (λ x → Fin (S x)) → Fin (finiteSum S)
  canonicalΣ S = iso.inv (_≅_.isIso (isoCanonicalΣ S))

  isIsoCanonicalΣ : {n : ℕ} (S : Fin n → ℕ) → iso (canonicalΣ S)
  isIsoCanonicalΣ S = isoInv (_≅_.isIso (isoCanonicalΣ S))


--Now the canonical order

  Σorder2Alt : {n : ℕ} (S : Fin n → ℕ) {a : Fin n} {m : ℕ} {b₁ b₂ : Fin m} (p : m ≡ S a) → 
               canonicalΣ S (a , transport Fin p b₁) << canonicalΣ S (a , transport Fin p b₂) ↔ b₁ << b₂
  Σorder2Alt S {a} {.(s _)} {fzero} {fzero} = {!!}
  Σorder2Alt S {a} {.(s _)} {fzero} {fsucc b₂} = {!!}
  Σorder2Alt S {a} {.(s _)} {fsucc b₁} {b₂} = {!!}

  Σorder2 : {n : ℕ} (S : Fin n → ℕ) {a : Fin n} {b₁ b₂ : Fin (S a)} → canonicalΣ S (a , b₁) << canonicalΣ S (a , b₂) ↔ b₁ << b₂ 
  Σorder2 {O} S {a = a} = Fin⊥ a
  Σorder2 {s n} S {fzero} {b₁} {b₂} = {!!}
  Σorder2 {s n} S {fsucc a} {b₁} {b₂} = {!!}

  ΣorderAux : {n : ℕ} (S : Fin (s n) → ℕ) {a : Fin n} {b₁ : Fin (S fzero)} {b₂ : Fin (S (fsucc a))} 
              → canonicalΣ S (fzero , b₁) << canonicalΣ S (fsucc a , b₂)
  ΣorderAux S {b₂ = b₂} = {!!}

  Σorder1 : {n : ℕ} (S : Fin n  → ℕ) {a₁ a₂ : Fin n} → {b₁ : Fin (S a₁)} → {b₂ : Fin (S a₂)} → a₁ << a₂ → canonicalΣ S (a₁ , b₁) << canonicalΣ S (a₂ , b₂) 
  Σorder1 S {fzero} {fzero} = λ () 
  Σorder1 S {fzero} {fsucc a₂} = λ _ → {!!}
  Σorder1 S {fsucc a₁} = {!!}
  
  canonicalΣorder : {n : ℕ} (S : Fin n → ℕ) {a₁ a₂ : Fin n} {b₁ : Fin (S a₁)} {b₂ : Fin (S a₂)} → 
                    (canonicalΣ S (a₁ , b₁) < canonicalΣ S (a₂ , b₂)) ↔ ((a₁ < a₂) ∨ Σ (a₁ ≡ a₂) (λ p → transport Fin (ap S p) b₁ < b₂ ))
  canonicalΣorder S = {!!} , 
                      λ { (left q) → Σorder1 S q ; (right (refl , q)) → ∧right (Σorder2 S) q}

--{!!} ,                       canonicalΣorder {n} S {a₁} {a₂} {b₁} {b₂} = ? , ?

-}

{-  canonicalΣorder {O} S {a₁ = x} =  Fin⊥ x
  canonicalΣorder {s n} S {fzero} {fzero} {b₁} {b₂} = ↔Trans (b₁ < b₂) 
                                                             (Σorder2 S) 
                                                             ((λ q → right (refl , q)) , 
                                                               λ { (left x) → efql x ; (right (p , q)) →
                                                                     ≡order {x₁ = transport Fin (ap S p) b₁} {x₂ = b₁} {y₂ = b₂} 
                                                                            (transportEqualPaths {b = b₁} (ap S p) refl UIP) refl q})
  canonicalΣorder {s n} S {fzero} {fsucc a₂} = (λ _ → left *) , λ _ → {!!}
  canonicalΣorder {s n} S {fsucc a₁} = {!!}
-}


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