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






--Things I don't know what to do with

injectiveFsucc : {n : ℕ} → injective (fsucc {n})
injectiveFsucc {n} {x} {y} refl = refl

finiteSum : {n : ℕ} (f : Fin n → ℕ) → ℕ
finiteSum {O} _ = O
finiteSum {s n} f = f (fzero) + finiteSum (f o fsucc)





--Prove finiteness of canonical finite sets
instance
  canonicalFOSet : {n : ℕ} → FOSet (Fin n)
  canonicalFOSet {n} = record { cardinal = n ; funFO = Id ; isIsoFO = isoId }







module ArithmeticForCanonicalSets where


--First we define the function canoncialΣ : Σ Fin Fin → Fin

  Fin+Left : {m n : ℕ} → Fin m → Fin (m + n)
  Fin+Left fzero = fzero
  Fin+Left (fsucc a) = fsucc (Fin+Left a)
  
  Fin+Right : {m n : ℕ} → Fin n → Fin (m + n)
  Fin+Right {O} = Id
  Fin+Right {s m} = fsucc o Fin+Right

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
  equalFin+LeftRight : {m n : ℕ} → 
                       (iso.inv isoFinSucc  o (∨Nat Id Fin+LeftRight) o ∨Assoc o (∨Nat FinSucc Id)) 
                       ≡ Fin+LeftRight {m = s m} {n = n}

  equalFin+LeftRight = funext (λ { (left fzero) → refl ; (left (fsucc a)) → refl ; (right a) → refl})


  isoFin+LeftRight : {m n : ℕ} → iso (Fin+LeftRight {m = m} {n = n})

  isoFin+LeftRight {O} = record { inv = λ a → right a ; 
                                  invLeft = λ b → refl ; 
                                  invRight = λ { (left ()) ; (right a) → refl} }

  isoFin+LeftRight {s m} = transport iso equalFin+LeftRight 
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
  equalCanonicalΣ : {n : ℕ} (S : Fin (s n) → ℕ) 
                    → (Fin+LeftRight  o (∨Nat Id (canonicalΣ (S o fsucc))) o (functionAux S)) ≡ canonicalΣ S
  equalCanonicalΣ S = funext (λ { (fzero , b) → refl ; (fsucc a , b) → refl})



  isIsoCanonicalΣ : {n : ℕ} (S : Fin n → ℕ) → iso (canonicalΣ S)

  isIsoCanonicalΣ {O} S = record { inv = λ () ; 
                                   invLeft = λ () ; 
                                   invRight = λ {(() , _)} }

  isIsoCanonicalΣ {s n} S = transport iso (equalCanonicalΣ S) 
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

module FiniteUnionOfFiniteSets where

--We only need three results from the module on canonical finite sets
  open ArithmeticForCanonicalSets using (canonicalΣ; isIsoCanonicalΣ; canonicalΣorder)


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
                   record { cardinal = finiteSum (Σcardinal A B) ; 
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
                  (∨Nat↔ ↔Refl let C = λ p → transport Fin (ap (Σcardinal A B) p) (Σfibre A B b₁) < Σfibre A B b₂ 
                               in ↔Trans (Σ (a₁ ≡ a₂) (λ p → C (ap f p)))  
                                       (↔Sym (injectiveEqual C (injectiveIso isIsoFO))) 
                                         ((λ {(refl , q) → (refl , ∧right (ΣfibreOrder {A = A} {b₁ = b₁}) q)}) , 
                                          (λ {(refl , q) → (refl , ∧left (ΣfibreOrder {A = A} {b₁ = b₁}) q)})) )



open FiniteUnionOfFiniteSets using (FOΣ; Σorder)




--Morphisms between FOSet

record HomFO {A B : Set} {{Afinite : FOSet A}} {{Bfinite : FOSet B}} (f : A → B) : Set where
  field
    isoHomFO : iso f
    orderPreserving : {x y : A} → x << y ↔ f x << f y

open HomFO {{...}} public





--We construct the basic instance needed for FOSet to be a category

instance
  HomFOId : {A : Set} {{Afinite : FOSet A}} → HomFO (λ (x : A) → x)
  HomFOId = record { isoHomFO = isoId ; 
                     orderPreserving = ↔Refl }


  HomFOComp : {A B C : Set} {{_ : FOSet A}} {{_ : FOSet B}} {{_ : FOSet C}} 
              {f : A → B} {g : B → C} (homf : HomFO f) (homg : HomFO g)
              → HomFO (g o f)

  HomFOComp {f = f}
            record { isoHomFO = isof ; orderPreserving = orderf } 
            record { isoHomFO = isog ; orderPreserving = orderg } 
          = record { isoHomFO = isoComp isof isog ; 
                     orderPreserving = λ {x} {y} → ↔Trans (f x << f y) orderf orderg }



--We construct the isomorphism needed for the definition of operads

η₁ : (B : Fin (s O) → Set) {{Bfinite : {x : Fin (s O)} → FOSet (B x)}} → B fzero → Σ (Fin (s O)) B
η₁ B x = fzero , x




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