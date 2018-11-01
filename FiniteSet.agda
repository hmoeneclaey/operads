module FiniteSet where

--Module containing basic definitions
open import Data




--We define canonical finite sets, together with their total order


--Intuitively fzero is 0, and fsucc n t is the successor of t.

data Fin : ℕ → Set where
  fzero : (n : ℕ) → Fin (s n)
  fsucc : (n : ℕ) → Fin n → Fin (s n)

_<_ : {n : ℕ} → Fin n → Fin n → Set
t < fzero n = ⊥
fzero n < fsucc n t = ⊤
fsucc n t₁ < fsucc n t₂ = t₁ < t₂





--We define (small) finite totally ordered sets as instance classes

record FOSet (A : Set) : Set where
  field
    cardinal : ℕ
    funFO : A → Fin cardinal
    isIsoFO : iso funFO  

open FOSet {{...}} public

--Defining canonical FOSet
instance 
  canonicalFOSet : {n : ℕ} → FOSet (Fin n)
  canonicalFOSet {n} = record { cardinal = n ; funFO = Id ; isIsoFO = isoId }

--Defining the order on them

_<<_ : {A : Set} {{Afinite : FOSet A}} → A → A → Set
_<<_ {A} {{Afinite}} x y = funFO x < funFO y

--The larger the number, the more binding
infix 56 _<<_






--We show that finite sets are stable by Σ



--Some arithmetic with canonical finite sets THIS SECTION SHOULD BE HEVILY CHANGED AT SOME POINTS

Fin⊥ : Fin O → ⊥
Fin⊥ ()

Fin⊤ : (x : Fin (s O)) → x ≡ fzero O
Fin⊤ (fzero .O) = refl
Fin⊤ (fsucc .O x) = efql (Fin⊥ x)

finiteSum : {n : ℕ} (f : Fin n → ℕ) → ℕ
finiteSum {O} _ = O
finiteSum {s n} f = f (fzero n) + finiteSum (f o fsucc n)


module CanonicalIsoForSigma where

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
  canonicalΣorder = {!!}


open CanonicalIsoForSigma using (canonicalΣ) 
open CanonicalIsoForSigma using (isIsoCanonicalΣ) 
open CanonicalIsoForSigma using (canonicalΣorder)



Σcardinal : (A : Set) {{Afinite : FOSet A}} (B : A → Set) {{Bfinite : {a : A} → FOSet (B a)}} → Fin (cardinal {A}) → ℕ
Σcardinal A ⦃ record { cardinal = |A| ; 
                          funFO = f ; 
                          isIsoFO = record { inv = g ; 
                                             invLeft = invLeft ; 
                                             invRight = invRight } } ⦄ B 
                 = λ n → cardinal {B (g n)}


ΣFibre : (A : Set) {{Afinite : FOSet A}} (B : A → Set) {{Bfinite : {a : A} → FOSet (B a)}} → {a : A} → B a → Fin (Σcardinal A B (funFO a))
ΣFibre A ⦃ record { cardinal = |A| ; 
                    funFO = f ; 
                    isIsoFO = record { inv = g ; invLeft = invLeft ; invRight = invRight } } ⦄ B {a = a} 
               = λ b → transport (λ a → Fin (cardinal {B a})) (invRight a) (funFO {B a} b)

instance 
  finiteΣ : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} → FOSet (Σ A B)
  finiteΣ {A} {{Afinite}} {B} {{Bfinite}} 
              = let S = Σcardinal A B in let F = ΣFibre A B in
                   record { cardinal = finiteSum (Σcardinal A B) ; 
                            funFO = (canonicalΣ S) o (Σfun {B₁ = B} {B₂ = λ n → Fin (S n)} funFO F) ;
                            isIsoFO = isoComp 
                                      (isoΣfun (isIsoFO)
                                      λ a → isoComp (isIsoFO {B a}) (isoTransport _ _)) 
                                      (isIsoCanonicalΣ S) }
                 




--We want an explicit description of the order on Σ types


{-transportOrder : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} {a₁ a₂ : A} 
                 (p : a₁ ≡ a₂) {b₁ b₂ : B a₁} → b₁ << b₂ → transport B p b₁ << transport B p b₂
transportOrder refl = λ x → x-}

ΣFibreOrder : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} {a : A} {b₁ b₂ : B a} → b₁ << b₂ → ΣFibre A B b₁ < ΣFibre A B b₂
ΣFibreOrder = {!!}

ΣFibreOrderRev : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} {a : A} {b₁ b₂ : B a} → ΣFibre A B b₁ < ΣFibre A B b₂ → b₁ << b₂
ΣFibreOrderRev = {!!}


Σorder : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} 
         → {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}  
         → (a₁ , b₁) << (a₂ , b₂) ↔ (a₁ << a₂ ∨ Σ (a₁ ≡ a₂) (λ p → transport B p b₁ << b₂))
Σorder {A} {{Afinite}} {B} ⦃ Bfinite ⦄ {a₁} {a₂} {b₁} {b₂} 
       = let S = Σcardinal A B in 
         let F = ΣFibre A B in 
         let f : A → Fin (cardinal {A})
             f = funFO
         in
         ↔Trans ((f a₁ < f a₂) ∨ (Σ (f a₁ ≡ f a₂) (λ p → transport Fin (ap S p) (F b₁) < F b₂)))
           (canonicalΣorder S {a₁ = f a₁} {a₂ = f a₂} {b₁ = F b₁} {b₂ = F b₂}) 
           (↔natural∨ ↔Refl ( let C = λ p → transport Fin (ap (Σcardinal A B) p) (ΣFibre A B b₁) < ΣFibre A B b₂ in
                              let u₁ : Σ (f a₁ ≡ f a₂) C → Σ (a₁ ≡ a₂) (C o (ap f))
                                  u₁ = iso.inv (isoΣfun {B₂ = C} {f = (ap f)} 
                                                        {F = Id} {!!} (λ _ → isoId)) 
                              in ((λ {(refl , q) → refl , ΣFibreOrderRev {A = A} {b₁ = b₁} q}) o u₁) ,
                             (λ {(refl , q) → refl , ΣFibreOrder {A = A} {b₁ = b₁} q }))) 







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