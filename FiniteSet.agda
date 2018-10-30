module FiniteSet where

--Module containing basic definitions
open import Data




--We define canonical finite sets, together with their total order


--Intuitively fzero is 0, and fsucc n t is the successor of t.

data Fin : ℕ → Set where
  fzero : (n : ℕ) → Fin (s n)
  fsucc : (n : ℕ) → Fin n → Fin (s n)

--NOT USED FOR NOW
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
  canonicalFOSet {n} = record { cardinal = n ; isFinite = isoRefl }


--We show that finite sets are stable by Σ



--Some arithmetic with canonical finite sets


--QUESTION : should I define this
Fin⊥ : Fin O → ⊥
Fin⊥ ()

--NOT USED FOR NOW
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
Fin+ {s m} {n} = isoTrans (⊤ ∨ Fin (m + n)) FinSucc 
                 (isoTrans (⊤ ∨ (Fin m ∨ Fin n)) (iso∨ isoRefl (Fin+ {m})) 
                 (isoTrans ((⊤ ∨ Fin m) ∨ Fin n) ∨Assoc (iso∨ (isoSym FinSucc) isoRefl)))


finiteSum : {n : ℕ} (f : Fin n → ℕ) → ℕ
finiteSum {O} _ = O
finiteSum {s n} f = f (fzero n) + finiteSum (f o fsucc n)

--The main lemma

isoCanonicalΣAux : {n : ℕ} (f : Fin (s n) → ℕ) 
                 → (Fin (f (fzero n)) ∨ Σ (Fin n) (λ a → Fin (f (fsucc n a)))) 
                 ≅ Σ (Fin (s n)) (λ x → Fin (f x))
isoCanonicalΣAux {n} f = record { isoFun = λ { (left x) → fzero n , x ; (right (k , x)) → (fsucc n k) , x} ; 
                              isIso = record { inv = λ { (fzero n , x) → left x ; (fsucc n k , x) → right (k , x)} ; 
                                               invLeft = λ { (fzero n , x) → refl ; (fsucc n k , x) → refl} ; 
                                               invRight = λ { (left x) → refl ; (right (k , x)) → refl} } }

isoCanonicalΣ : {n : ℕ} (f : Fin n → ℕ) → Fin (finiteSum f) ≅ Σ (Fin n) (λ x → Fin (f x))
isoCanonicalΣ {O} _ = iso⊥ Fin⊥ (λ { (a , _) → Fin⊥ a}) 
isoCanonicalΣ {s n} f = isoTrans (Fin (f (fzero n)) ∨ Fin (finiteSum (f o fsucc n))) 
                        Fin+ (isoTrans (Fin (f (fzero n)) ∨ Σ (Fin n) (Fin o (f o fsucc n)))
                               (iso∨ isoRefl (isoCanonicalΣ (f o fsucc n)))
                               (isoCanonicalΣAux f))



--Stabilitiy by Sigma
--QUESTION What should I use instead of {{a : A → Bfinite (B a)}} ?
instance 
  finiteΣ : {A : Set} (Afinite : FOSet A) {B : A → Set} (Bfinite : (a : A) → FOSet (B a)) → FOSet (Σ A B)
  finiteΣ {A} record { cardinal = |A| ; 
                       isFinite = record { isoFun = f ; isIso = isof } } 
          {B} Bfinite = let S : Fin |A| → ℕ
                            S = λ (a : Fin |A|)  → cardinal {B (f a)} {{Bfinite (f a)}}  --weird
                            in record { cardinal = finiteSum S ; 
                                        isFinite = isoTrans (Σ (Fin |A|) (B o f)) 
                                            (isoTrans (Σ (Fin |A|) (λ a → Fin (S a))) 
                                                      (isoCanonicalΣ S) (isoΣfibre {B₂ = B o f} (λ a → isFinite {B (f a)} {{Bfinite (f a)}}))) --weird
                                            (isoΣbase f isof) }




--Morphisms between FOSet

--We encounter a problem

{-
isoAux : {A B : Set} {{Afinite : FOSet A}} {{Bfinite : FOSet B}} {f : A → B} → iso f → Fin (cardinal {A}) → Fin (cardinal {B}) 
isoAux = {!!}

record HomFOSet {A B : Set} {{Afinite : FOSet A}} {{Bfinite : FOSet B}} (f : A → B) : Set where
  field
    isIsoFOSet : iso f
    orderPreserving : let ψA = _≅_.isoFun (isFinite {A} {{Afinite}}) in 
                      let ψB = _≅_.isoFun (isFinite {B} {{Bfinite}}) in 
                      (a : Fin (cardinal {A})) → f (ψA a) ≡ ψB (isoAux isIsoFOSet a) 
-}

