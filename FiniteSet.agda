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

{-
order : {A : Set} {{Afinite : FOSet A}} → A → A → Set
order x y = x << y
-}


--Prove finiteness of canonical finite sets
instance
  canonicalFOSet : {n : ℕ} → FOSet (Fin n)
  canonicalFOSet {n} = record { cardinal = n ; funFO = Id ; isIsoFO = isoId }




--Very basic facts about the order

<Irefl : {n : ℕ} (a : Fin n) → ¬ (a < a)
<Irefl fzero = Id
<Irefl (fsucc a) = <Irefl a

<<Irefl : {A : Set} {{_ : FOSet A}} (a : A) → ¬ (a << a)
<<Irefl {A} a = λ q → <Irefl (funFO a) q

<MinFzero : {m : ℕ} {n : Fin (s m)} → ¬ (n << fzero)
<MinFzero {n = fzero} = Id
<MinFzero {n = fsucc n} = Id

<IreflEqual : {n : ℕ} {x y : Fin n} → x ≡ y → ¬ (x << y)
<IreflEqual {x = x} refl = <Irefl x

<Total : {m : ℕ} {x y : Fin m} → ¬ (x << y) → ¬ (y << x) → x ≡ y
<Total {x = fzero} {fzero} = λ _ _ → refl
<Total {x = fzero} {fsucc y} p = efql (p *)
<Total {x = fsucc x} {fzero} _ p = efql (p *)
<Total {x = fsucc x} {fsucc y} p q = ap fsucc (<Total p q)

isSucc : {m : ℕ} {x : Fin (s m)} → fzero << x → Σ (Fin m) (λ y → x ≡ fsucc y)
isSucc {x = fzero} () 
isSucc {x = fsucc a} _ = a , refl

isFzero : {m : ℕ} {x : Fin (s m)} → ((y : Fin (s m)) → ¬ (y << x)) → x ≡ fzero
isFzero {x = fzero} _ = refl
isFzero {x = fsucc x} Hyp = efql (Hyp fzero *)




--Injectivity of successor

injectiveFsucc : {n : ℕ} → injective (fsucc {n})
injectiveFsucc {n} {x} {y} refl = refl

finiteSum : {n : ℕ} (f : Fin n → ℕ) → ℕ
finiteSum {O} _ = O
finiteSum {s n} f = f (fzero) + finiteSum (f o fsucc)





--An interlude about finite product


Prod : ∀ {k} (X : Set k) → ℕ → Set k
Prod X O = ⊤
Prod X (s n) = X ∧ Prod X n


module _ {k} {X : Set k} where

  prodFun : ∀ {n : ℕ} → Prod X n → (Fin n → X) 
  prodFun {O} = λ _ ()
  prodFun {s n} = λ { (x , y) fzero → x ;
                    (x , y) (fsucc n) → prodFun y n }

  invProdFun : ∀ {n : ℕ} → (Fin n → X) → Prod X n
  invProdFun {O} = λ _ → *
  invProdFun {s n} = λ x → (x fzero) , (invProdFun (x o fsucc))

  invLeftProdFun : ∀ {n : ℕ} (x : Fin n → X) (m : Fin n) → x m ≡ prodFun (invProdFun x) m
  invLeftProdFun {O} = λ _ ()
  invLeftProdFun {s n} x = λ { fzero → refl ;
                               (fsucc m) → invLeftProdFun (x o fsucc) m}

  invRightProdFun : ∀ {n : ℕ} (a : Prod X n) → a ≡ invProdFun (prodFun a)
  invRightProdFun {O} = λ _ → refl
  invRightProdFun {s n} = λ {(x , y) → ap (λ y₁ → x , y₁) (invRightProdFun y)}

  isoProdFun : ∀ {n : ℕ} → iso (prodFun {n})
  isoProdFun = record { inv = invProdFun ;
                        invLeft = funext o invLeftProdFun ;
                        invRight = invRightProdFun }






Fin+Left : {m n : ℕ} → Fin m → Fin (m + n)
Fin+Left fzero = fzero
Fin+Left (fsucc a) = fsucc (Fin+Left a)
  
Fin+Right : {m n : ℕ} → Fin n → Fin (m + n)
Fin+Right {O} = Id
Fin+Right {s m} = fsucc o Fin+Right





--module ArithmeticForCanonicalSets where


--First we define the function canoncialΣ : Σ Fin Fin → Fin

canonicalΣ : {n : ℕ} (S : Fin n → ℕ) → Σ (Fin n) (λ x → Fin (S x)) → Fin (finiteSum S)
canonicalΣ S (fzero , b) = Fin+Left b
canonicalΣ S (fsucc a , b) = Fin+Right (canonicalΣ (S o fsucc) (a , b))


  --We show that Fin n ∨ Fin m is isomorphic to Fin m + n

FinSucc : {m : ℕ} → Fin (s m) → Fin (s O) ∨ Fin m
FinSucc fzero = left fzero
FinSucc (fsucc a) = right a

isoFinSucc : {m : ℕ} → iso (FinSucc {m = m})
isoFinSucc = record { inv = ∨Elim (λ _ → fzero) fsucc ; 
                        invLeft = λ { (left fzero) → refl ; (right x) → refl} ; 
                        invRight = λ { fzero → refl ; (fsucc x) → refl} }

Fin+LeftRight : {m n : ℕ} → Fin m ∨ Fin n → Fin (m + n) 
Fin+LeftRight = ∨Elim Fin+Left Fin+Right


  --This equality is useful for inductive case
equalFin+LeftRight : {m n : ℕ} → (x : Fin (s m) ∨ Fin n) →
                       (iso.inv isoFinSucc  o (∨Nat Id Fin+LeftRight) o ∨Assoc o (∨Nat FinSucc Id)) x
                       ≡ Fin+LeftRight x

equalFin+LeftRight (left fzero) = refl
equalFin+LeftRight (left (fsucc a)) = refl
equalFin+LeftRight (right a) = refl


isoFin+LeftRight : {m n : ℕ} → iso (Fin+LeftRight {m = m} {n = n})

isoFin+LeftRight {O} = record { inv = λ a → right a ; 
                                invLeft = λ b → refl ; 
                                invRight = λ { (left ()) ; (right a) → refl} }

isoFin+LeftRight {s m} = iso≡ext equalFin+LeftRight 
                         (isoComp {f = ∨Nat Id Fin+LeftRight o ∨Assoc o ∨Nat FinSucc Id} {g = ∨Elim (λ _ → fzero) fsucc} 
                         (isoComp {f = ∨Assoc o ∨Nat FinSucc Id} {g = ∨Nat Id Fin+LeftRight}
                              (isoComp {f = ∨Nat FinSucc Id} {g = ∨Assoc} 
                                (iso∨Nat isoFinSucc isoId) 
                                iso∨Assoc) 
                              (iso∨Nat isoId isoFin+LeftRight)) 
                           (isoInv isoFinSucc)) 



--Here we show that canonicalΣ is an isomorphism
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

  

--We use function extensionnality, but we can probably deal without
equalCanonicalΣ : {n : ℕ} (S : Fin (s n) → ℕ) (x : Σ (Fin (s n)) (λ k → Fin (S k)))
                    → (Fin+LeftRight  o (∨Nat Id (canonicalΣ (S o fsucc))) o (functionAux S)) x ≡ canonicalΣ S x
equalCanonicalΣ S (fzero , b) = refl
equalCanonicalΣ S (fsucc a , b) = refl



isIsoCanonicalΣ : {n : ℕ} (S : Fin n → ℕ) → iso (canonicalΣ S)

isIsoCanonicalΣ {O} S = record { inv = λ () ; 
                                 invLeft = λ () ; 
                                 invRight = λ {(() , _)} }

isIsoCanonicalΣ {s n} S = iso≡ext (equalCanonicalΣ S) 
                   (isoComp {f = (∨Nat Id (canonicalΣ (S o fsucc)) o functionAux S)} {g = ∨Elim Fin+Left Fin+Right} 
                      (isoComp {f = functionAux S} {g = ∨Nat (λ x → x) (canonicalΣ (S o fsucc))} 
                         (isoFunctionAux S) 
                         (iso∨Nat isoId (isIsoCanonicalΣ (S o fsucc)))) 
                         isoFin+LeftRight) 






--Now prove the order is the one we expect

Fin+LeftOrder : {m n : ℕ} → (b₁ b₂ : Fin m) 
                → Fin+Left {n = n} b₁ << Fin+Left {n = n} b₂ ↔ b₁ << b₂
Fin+LeftOrder fzero fzero = ↔Refl
Fin+LeftOrder fzero (fsucc b₂) = (λ _ → *) , λ _ → *
Fin+LeftOrder (fsucc b₁) fzero = (λ ()) , (λ ())
Fin+LeftOrder {m = s m} {n = n} (fsucc b₁) (fsucc b₂) = Fin+LeftOrder b₁ b₂


Fin+OrderInf : {m n : ℕ} (b₁ : Fin m) (b₂ : Fin n) → Fin+Left b₁ < Fin+Right b₂
Fin+OrderInf fzero b₂ = *
Fin+OrderInf (fsucc b₁) b₂ = Fin+OrderInf b₁ b₂


Fin+OrderSup : {m n : ℕ} (b₁ : Fin m) (b₂ : Fin n) → ¬ (Fin+Right b₁ < Fin+Left b₂)
Fin+OrderSup b₁ fzero = Id
Fin+OrderSup b₁ (fsucc b₂) = Fin+OrderSup b₁ b₂


Fin+RightOrder : {m n : ℕ} → (b₁ b₂ : Fin n) 
                 → Fin+Right {m = m} b₁ << Fin+Right {m = m} b₂ ↔ b₁ << b₂
Fin+RightOrder {O} b₁ b₂ = ↔Refl
Fin+RightOrder {s m} b₁ b₂ = Fin+RightOrder {m} b₁ b₂



canonicalΣorder : {n : ℕ} (S : Fin n → ℕ) {a₁ a₂ : Fin n} {b₁ : Fin (S a₁)} {b₂ : Fin (S a₂)} 
                  → (canonicalΣ S (a₁ , b₁) << canonicalΣ S (a₂ , b₂)) 
                  ↔ ((a₁ < a₂) ∨ Σ (a₁ ≡ a₂) (λ p → transport Fin (ap S p) b₁ < b₂ ))

canonicalΣorder S {fzero} {fzero} {b₁} {b₂} = ↔Trans (b₁ < b₂) 
                                                     (Fin+LeftOrder b₁ b₂)  
                                                     ((λ q → right (refl , q)) , λ { (left ()) ; (right (refl , q)) → q})

canonicalΣorder S {fzero} {fsucc a₂} {b₁} {b₂} = (λ _ → left *) , 
                                                  λ _ → Fin+OrderInf b₁ _

canonicalΣorder S {fsucc a₁} {fzero} {b₁} {b₂} = (λ q → efql (Fin+OrderSup _ b₂ q)) , 
                                                 λ { (left ()) ; (right (() , _)) }
  
canonicalΣorder S {fsucc a₁} {fsucc a₂} {b₁} {b₂} 
                         = ↔Trans (canonicalΣ (S o fsucc) (a₁ , b₁) << canonicalΣ (S o fsucc) (a₂ , b₂))
                                  (Fin+RightOrder {m = S fzero} _ _) 
                                  (↔Trans (a₁ << a₂ ∨ Σ (a₁ ≡ a₂) (λ p → transport Fin (ap (S o fsucc) p) b₁ << b₂))
                                          (canonicalΣorder (S o fsucc) {a₁} {a₂}) 
                                          (∨Nat↔ ↔Refl 
                                                 (let C = λ (p : fsucc a₁ ≡ fsucc a₂) → transport Fin (ap S p) b₁ < b₂ 
                                                  in ↔Trans (Σ (a₁ ≡ a₂) (C o ap fsucc)) 
                                                             ((λ {(refl , q) → refl , q}) , 
                                                               λ {(refl , q) → refl , q}) 
                                                             (injectiveEqual C injectiveFsucc))))









--We show that a finite union of finite sets is finite, and give an explicit order on Σ A B

--module FiniteUnionOfFiniteSets where

--We only need three results from the module on canonical finite sets
--  open ArithmeticForCanonicalSets using (canonicalΣ; isIsoCanonicalΣ; canonicalΣorder)


Σcardinal : (A : Set) {{Afinite : FOSet A}} (B : A → Set) {{Bfinite : {a : A} → FOSet (B a)}} → Fin (cardinal {A}) → ℕ
Σcardinal A ⦃ record { cardinal = |A| ; 
                       funFO = f ; 
                       isIsoFO = record { inv = g ; 
                                          invLeft = invLeft ; 
                                          invRight = invRight } } ⦄ B 
               = λ n → cardinal {B (g n)}


Σfibre : (A : Set) {{Afinite : FOSet A}} (B : A → Set) {{Bfinite : {a : A} → FOSet (B a)}} 
         → {a : A} → B a → Fin (Σcardinal A B (funFO a))

Σfibre A ⦃ record { cardinal = |A| ; 
                    funFO = f ;
                    isIsoFO = record { inv = g ; invLeft = invLeft ; invRight = invRight } } ⦄ B {a = a} 
             = λ b → transport (λ a → Fin (cardinal {B a})) (invRight a) (funFO {B a} b)


instance 
  FOΣ : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} → FOSet (Σ A B)

  FOΣ {A} {{Afinite}} {B} {{Bfinite}} 
            = let S = Σcardinal A B in let F = Σfibre A B in
                 record { cardinal = finiteSum S ; 
                          funFO = (canonicalΣ S) o (Σfun {B₁ = B} {B₂ = λ n → Fin (S n)} funFO F) ;
                          isIsoFO = isoComp 
                                    (isoΣfun (isIsoFO)
                                    λ a → isoComp (isIsoFO {B a}) 
                                                  (isoTransport (λ a → Fin (cardinal {B a})) (iso.invRight (isIsoFO {A}) a))) 
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


Σord : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}}
         → (a₁ : A) (b₁ : B a₁) (a₂ : A) (b₂ : B a₂) → Set
Σord {B = B} a₁ b₁ a₂ b₂ = (a₁ << a₂ ∨ Σ (a₁ ≡ a₂) (λ p → transport B p b₁ << b₂))

Σorder : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} 
         → {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}  
         → (a₁ , b₁) << (a₂ , b₂) ↔ Σord a₁ b₁ a₂ b₂

Σorder {A} {{Afinite}} {B} ⦃ Bfinite ⦄ {a₁} {a₂} {b₁} {b₂} 
         = let S = Σcardinal A B in 
           let F = Σfibre A B in 
           let f : A → Fin (cardinal {A})
               f = funFO
           in
           ↔Trans ((f a₁ < f a₂) ∨ (Σ (f a₁ ≡ f a₂) (λ p → transport Fin (ap S p) (F b₁) < F b₂)))
             (canonicalΣorder S {a₁ = f a₁} {a₂ = f a₂} {b₁ = F b₁} {b₂ = F b₂}) 
                  (∨Nat↔ ↔Refl let C = λ p → transport Fin (ap (Σcardinal A B) p) (Σfibre A B b₁) < Σfibre A B b₂ 
                               in ↔Trans (Σ (a₁ ≡ a₂) (λ p → C (ap f p)))  
                                       (↔Sym (injectiveEqual C (injectiveIso isIsoFO))) 
                                             ((λ {(refl , q) → (refl , ∧right (ΣfibreOrder {A = A} {b₁ = b₁}) q)}) , 
                                              (λ {(refl , q) → (refl , ∧left (ΣfibreOrder {A = A} {b₁ = b₁}) q)})) )



--open FiniteUnionOfFiniteSets using (FOΣ; Σord; Σorder)

ord : (A : Set) {{_ : FOSet A}} → A → A → Set
ord A x y = x << y 

ΣorderSnd : {A : Set} {{Afinite : FOSet A}} {B : A → Set} {{Bfinite : {a : A} → FOSet (B a)}} 
            {a : A} → {b₁ b₂ : B a} 
            → b₁ << b₂ ↔ ord (Σ A B) (a , b₁) (a , b₂)
ΣorderSnd {B = B} {a = a} {b₁ = b₁} {b₂ = b₂} = ↔Trans (Σord a b₁ a b₂) 
                                                ((λ p → right (refl , p)) , 
                                                 λ { (left q) → efql (<<Irefl a q) ; (right (refl , q)) → q}) 
                                                (↔Sym (Σorder {B = B}) )


