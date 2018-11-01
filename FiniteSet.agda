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


--Prove finiteness of canonical finite sets
instance
  canonicalFOSet : {n : ℕ} → FOSet (Fin n)
  canonicalFOSet {n} = record { cardinal = n ; funFO = Id ; isIsoFO = isoId }






--Some arithmetic with canonical finite sets THIS SECTION SHOULD BE CHANGED AT SOME POINT

finiteSum : {n : ℕ} (f : Fin n → ℕ) → ℕ
finiteSum {O} _ = O
finiteSum {s n} f = f (fzero) + finiteSum (f o fsucc)


module ArithmeticForCanonicalSets where

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

  canonicalΣ : {n : ℕ} (S : Fin n → ℕ) → Σ (Fin n) (λ x → Fin (S x)) → Fin (finiteSum S)
  canonicalΣ = {!!}

  isIsoCanonicalΣ : {n : ℕ} (S : Fin n → ℕ) → iso (canonicalΣ S)
  isIsoCanonicalΣ S = {!!}

  canonicalΣorder : {n : ℕ} (S : Fin n → ℕ) {a₁ a₂ : Fin n} {b₁ : Fin (S a₁)} {b₂ : Fin (S a₂)} →
                    (canonicalΣ S (a₁ , b₁) < canonicalΣ S (a₂ , b₂)) ↔ ((a₁ < a₂) ∨ Σ (a₁ ≡ a₂) (λ p → transport Fin (ap S p) b₁ < b₂ ))
  canonicalΣorder = {!!}


 {-
  Fin⊥ : Fin O → ⊥
  Fin⊥ ()

  Fin⊤ : (x : Fin (s O)) → x ≡ fzero O
  Fin⊤ (fzero .O) = refl
  Fin⊤ (fsucc .O x) = efql (Fin⊥ x)

  FinSucc : {m : ℕ} → Fin(s m) ≅ ⊤ ∨ Fin m
  FinSucc {m} = record { isoFun = λ { (fzero n) → left * ; (fsucc n x) → right x} ; 
                         isIso = record { inv = λ { (left x) → fzero m ; (right x) → fsucc m x} ; 
                                    invLeft = λ { (left *) → refl ; (right x) → refl} ; 
                                    invRight = λ { (fzero n) → refl ; (fsucc n x) → refl} } }

  Fin+ : {m n : ℕ} → Fin (m + n) ≅ Fin m ∨ Fin n
  Fin+ {O} {n} = iso∨⊥left Fin⊥
  Fin+ {s m} {n} = ≅Trans (⊤ ∨ Fin (m + n)) FinSucc 
                 (≅Trans (⊤ ∨ (Fin m ∨ Fin n)) (iso∨ ≅Refl (Fin+ {m})) 
                 (≅Trans ((⊤ ∨ Fin m) ∨ Fin n) ∨Assoc (iso∨ (≅Sym FinSucc) ≅Refl)))

  isoCanonicalΣAux : {n : ℕ} (f : Fin (s n) → ℕ) 
                 → (Fin (f (fzero n)) ∨ Σ (Fin n) (λ a → Fin (f (fsucc n a)))) 
                 ≅ Σ (Fin (s n)) (λ x → Fin (f x))
  isoCanonicalΣAux {n} f = record { isoFun = λ { (left x) → fzero n , x ; (right (k , x)) → (fsucc n k) , x} ; 
                              isIso = record { inv = λ { (fzero n , x) → left x ; (fsucc n k , x) → right (k , x)} ; 
                                               invLeft = λ { (fzero n , x) → refl ; (fsucc n k , x) → refl} ; 
                                               invRight = λ { (left x) → refl ; (right (k , x)) → refl} } }

  isoCanonicalΣ : {n : ℕ} (f : Fin n → ℕ) → Fin (finiteSum f) ≅ Σ (Fin n) (λ x → Fin (f x))
  isoCanonicalΣ {O} _ = iso⊥ Fin⊥ (λ { (a , _) → Fin⊥ a}) 
  isoCanonicalΣ {s n} f = ≅Trans (Fin (f (fzero n)) ∨ Fin (finiteSum (f o fsucc n))) 
                        Fin+ (≅Trans (Fin (f (fzero n)) ∨ Σ (Fin n) (Fin o (f o fsucc n)))
                               (iso∨ ≅Refl (isoCanonicalΣ (f o fsucc n)))
                               (isoCanonicalΣAux f))

--Those are the two we need for the moment
  canonicalΣ : {n : ℕ} (S : Fin n → ℕ) → Σ (Fin n) (λ x → Fin (S x)) → Fin (finiteSum S)
  canonicalΣ S = iso.inv (_≅_.isIso (isoCanonicalΣ S))

  dumbAux : ∀ {k l} {A : Set k} {B : Set l} {f : A → B} (isof : iso f) → iso (iso.inv isof)
  dumbAux {f = f} record { inv = g ; invLeft = invLeft ; invRight = invRight } = record { inv = f ; invLeft = invRight ; invRight = invLeft }

  isIsoCanonicalΣ : {n : ℕ} (S : Fin n → ℕ) → iso (canonicalΣ S)
  isIsoCanonicalΣ S = dumbAux (_≅_.isIso (isoCanonicalΣ S))

  canonicalΣorder : {n : ℕ} (S : Fin n → ℕ) {a₁ a₂ : Fin n} {b₁ : Fin (S a₁)} {b₂ : Fin (S a₂)} → 
                    (canonicalΣ S (a₁ , b₁) < canonicalΣ S (a₂ , b₂)) ↔ ((a₁ < a₂) ∨ Σ (a₁ ≡ a₂) (λ p → transport Fin (ap S p) b₁ < b₂ ))
  canonicalΣorder = {! !}
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
             (↔natural∨ ↔Refl (let C = λ p → transport Fin (ap (Σcardinal A B) p) (Σfibre A B b₁) < Σfibre A B b₂ in
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