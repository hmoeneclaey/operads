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
    isFinite : Fin cardinal ≅ A  

open FOSet {{...}} public


--Defining canonical FOSet
instance 
  canonicalFOSet : {n : ℕ} → FOSet (Fin n)
  canonicalFOSet {n} = record { cardinal = n ; isFinite = ≅Refl }


--We show that finite sets are stable by Σ



--Some arithmetic with canonical finite sets


--QUESTION : should I define this
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


finiteSum : {n : ℕ} (f : Fin n → ℕ) → ℕ
finiteSum {O} _ = O
finiteSum {s n} f = f (fzero n) + finiteSum (f o fsucc n)


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


instance 
  finiteΣ : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} → FOSet (Σ A B)
  finiteΣ {A} {{ record { cardinal = |A| ; 
                          isFinite = record { isoFun = f ; isIso = isof } } }}
          {B} {{Bfinite}} = let S : Fin |A| → ℕ
                                S = λ (a : Fin |A|)  → cardinal {B (f a)}
                            in record { cardinal = finiteSum S ; 
                                        isFinite = ≅Trans (Σ (Fin |A|) (B o f)) 
                                            (≅Trans (Σ (Fin |A|) (λ a → Fin (S a))) 
                                            (isoCanonicalΣ S) 
                                            (isoΣfibre (λ {a} → _≅_.isoFun (isFinite {B (f a)})) 
                                                        λ a → _≅_.isIso (isFinite {B (f a)})))
                                            (isoΣbase f isof) }



--About on the order on FOSet

_<<_ : {A : Set} {{Afinite : FOSet A}} → A → A → Set
_<<_ {A} {{Afinite}} x y = let g : A → Fin (cardinal {A})
                               g = iso.inv (_≅_.isIso (isFinite {A}))
                           in g x < g y

--The larger the number, the more binding
infix 56 _<<_


--We want an explicit description of the order on Σ types

Σorder : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} 
         → {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}  
         → (a₁ , b₁) << (a₂ , b₂) ↔ (a₁ << a₂ ∨ Σ (a₁ ≡ a₂) (λ p → transport B p b₁ << b₂))
Σorder = {!!}

--{A = A} ⦃ record { cardinal = |A| ; isFinite = record { isoFun = f ; isIso = record { inv = g ; invLeft = invLeft ; invRight = invRight } } } ⦄ {a₁ = a₁} {a₂ = a₂} = {!!}



--Morphisms between FOSet


record HomFO {A B : Set} {{Afinite : FOSet A}} {{Bfinite : FOSet B}} (f : A → B) : Set where
  field
    isIsoFO : iso f
    orderPreserving : {x y : A} → x << y ↔ f x << f y

open HomFO {{...}} public


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


