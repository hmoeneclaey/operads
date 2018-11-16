module Data where

open import Agda.Primitive



--Composition and identity

Id : ∀ {k} {A : Set k} → A → A
Id = λ x → x

_o_ : ∀ {k l m} {A : Set k} {B : A → Set l} {C : {a : A} → B a → Set m} 
      → (g : {a : A} → (b : B a) → C b) 
      → (f : (a : A) → B a) 
      → (a : A) → C (f a)
g o f = λ a → g (f a)

infixr 78 _o_


--Logical connectives

data ⊥ : Set where

record ⊤ : Set where
  constructor *

data Σ {k l} (A : Set k) (B : A → Set l) : Set (k ⊔ l) where
  _,_ : (a : A) → B a → Σ A B


--For some reason the data type sigma type check faster
{-
record Σ {k l} (A : Set k) (B : A → Set l) : Set (k ⊔ l)  where
  constructor _,_
  field 
    fst : A
    snd : B fst
-}
--infixr 56 _,_

_∧_ : ∀ {k l} → Set k → Set l → Set (k ⊔ l)
A ∧ B = Σ A (λ _ → B)

data _∨_ {k l} (A : Set k) (B : Set l) : Set (k ⊔ l) where
  left : A → A ∨ B
  right : B → A ∨ B

infix 36 _∨_

¬ : ∀ {k} → Set k → Set k
¬ A = A → ⊥

_↔_ : ∀ {k l} (A : Set l) (B : Set k) → Set (k ⊔ l)
A ↔ B = (A → B) ∧ (B → A)

infix 46 _↔_




--Some logical properties

efql : ∀ {k} {A : Set k} → ⊥ → A
efql ()

--For ↔

↔Refl : ∀ {k} {A : Set k} → A ↔ A
↔Refl = (λ a → a) , λ a → a

↔Trans : ∀ {k l m} {A : Set k} (B : Set l) {C : Set m} → A ↔ B → B ↔ C → A ↔ C
↔Trans B (f₁ , g₁) (f₂ , g₂) = (f₂ o f₁) , (g₁ o g₂)

↔Sym : ∀ {k l} {A : Set k} {B : Set l} → A ↔ B → B ↔ A
↔Sym (f₁ , f₂) = f₂ , f₁

--For ∨

∨Elim : ∀ {k l m} {A : Set k} {B : Set l} {C : Set m} → (A → C) → (B → C) → A ∨ B → C 
∨Elim f g (left a) = f a
∨Elim f g (right b) = g b 

∨Nat : ∀ {k l m n} {A : Set k} {B : Set l} {C : Set m} {D : Set n} → (A → C) → (B → D) → (A ∨ B) → (C ∨ D)
∨Nat f g = ∨Elim (left o f) (right o g)

∨Assoc : ∀ {k l m} {A : Set k} {B : Set l} {C : Set m} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
∨Assoc (left (left a)) = left a
∨Assoc (left (right b)) = right (left b)
∨Assoc (right c) = right (right c)

∨Nat↔ : ∀ {k l m n} {A : Set k} {B : Set l} {C : Set m} {D : Set n} → A ↔ C → B ↔ D → (A ∨ B) ↔ (C ∨ D)  
∨Nat↔ (f₁ , g₁) (f₂ , g₂) = ∨Nat f₁ f₂ , ∨Nat g₁ g₂


--For ∧

∧left : ∀ {k l} {A : Set k} {B : Set l} → A ∧ B → A
∧left (a , b) = a

∧right : ∀ {k l} {A : Set k} {B : Set l} → A ∧ B → B
∧right (a , b) = b


--For Σ
{-
ΣAssoc : ∀ {k l m} (A : Set k) (B : A → Set l) (C : Σ A B → Set m)
    → Σ A (λ a → Σ (B a) (λ b → C (a , b))) → Σ (Σ A B) C
ΣAssoc A B C (a , (b , c)) = ((a , b) , c)
-}



--Natural numbers

data ℕ : Set where
  O : ℕ
  s : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
O + n = n
s m + n = s(m + n)




--Strict equality

data _≡_ {k} {A : Set k} : A → A → Set k where
     refl : {a : A} → a ≡ a

Equal : ∀ {k} (A : Set k) (a b : A) → Set k
Equal A a b = a ≡ b

--Axiom K is implemented !
UIP : ∀ {k} {A : Set k} {x y : A} {p q : x ≡ y} → p ≡ q
UIP {p = refl} {q = refl} = refl

postulate funext : ∀ {k l} {A : Set k} {B : Set l} → {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g 




--Basic structure for strict equality

transport : ∀ {k l} {A : Set k} (B : A → Set l) {x y : A} → x ≡ y → B x → B y
transport B refl x = x

ap : ∀ {k l} {A : Set k} {B : Set l} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl 

≡Sym : ∀ {k} {A : Set k} {x y : A} → x ≡ y → y ≡ x
≡Sym refl = refl

≡Trans : ∀ {k} {A : Set k} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡Trans refl p = p

transportComp : ∀ {k l m n} {A₁ : Set k} {A₂ : Set l} {f : A₁ → A₂} {B₁ : A₁ → Set m} {B₂ : A₂ → Set n} {x y : A₁}
                      (p : x ≡ y) (F : {a₁ : A₁} → B₁ a₁ → B₂ (f a₁)) {b : B₁ x}
                      → F (transport B₁ p b) ≡ transport B₂ (ap f p) (F b)
transportComp refl F = refl

transportEqualPaths : ∀ {k l} {A : Set k} {B : A → Set l} {x y : A} {b : B x} (p q : x ≡ y) 
                      → p ≡ q → transport B p b ≡ transport B q b
transportEqualPaths p q refl = refl



--Results about Σ and equality

equalΣ : ∀ {k l} {A : Set k} {B : A → Set l} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} 
         (p : a₁ ≡ a₂) → transport B p b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂) 
equalΣ refl refl = refl

equal∧ : ∀ {k l} {A : Set k} {B : Set l} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
equal∧ refl refl = refl


--TODO
--I often use something similar, but not exactly that
{-
Σequal↔ : ∀ {k l} {A : Set k} {C₁ C₂ : {a₁ a₂ : A} → a₁ ≡ a₂ → Set l} 
          → ((a : A) → C₁ (refl {a = a}) ↔ C₂ (refl {a = a})) 
          → {a₁ a₂ : A} →  (Σ (a₁ ≡ a₂) C₁) ↔ (Σ (a₁ ≡ a₂) C₂)
Σequal↔ f {a₁} = ( λ {(refl , c) → refl , ∧left (f a₁) c} ), 
                 ( λ {(refl , c) → refl , (∧right (f a₁) c) } )
-}


--Dependent transport

deptransport : ∀ {k l m} {A : Set k} {B : A → Set l} (C : Σ A B → Set m) 
               {a₁ a₂ : A} {b : B a₁} (p : a₁ ≡ a₂) → C (a₁ , b) → C (a₂ , transport B p b)
deptransport C refl = Id


{-
deptransportEqual : ∀ {k l m} {A : Set k} {B : A → Set l} (C : Σ A B → Set m) {a₁ a₂ : A} {b : B a₁} {c : C (a₁ , b)} (p : a₁ ≡ a₂) 
                    → transport (λ a → Σ (B a) (λ b → C (a , b))) p (b , c) ≡ (transport B p b , deptransport C p c)
deptransportEqual C refl = refl
-}


--Definition of isomorphism

record iso {k l} {A : Set k} {B : Set l} (f : A → B) : Set (k ⊔ l) where
  field
    inv : B → A
    invLeft : (b : B) → b ≡ f (inv b)
    invRight : (a : A) → a ≡ inv (f a)

record _≅_ {k l} (A : Set k) (B : Set l) : Set (k ⊔ l) where
  field
    isoFun : A → B
    isIso : iso isoFun



--Basic results about isomorphisms


isoId : ∀ {k} {A : Set k} → iso (λ (x : A) → x)
isoId = record { inv = Id ; invLeft = λ b → refl ; invRight = λ a → refl }

isoComp : ∀ {k l m} {A : Set k} {B : Set l} {C : Set m} 
          {f : A → B} {g : B → C} → iso f → iso g → iso (g o f)
isoComp {f = f₁} {g = g₁} record { inv = f₂ ; invLeft = invf₁ ; invRight = invf₂ } 
                          record { inv = g₂ ; invLeft = invg₁ ; invRight = invg₂ } 
        = record { inv = f₂ o g₂ ; 
                 invLeft = λ b → ≡Trans {y = g₁ (g₂ b)} (invg₁ b) (ap g₁ (invf₁ (g₂ b))) ; 
                 invRight = λ a → ≡Trans {y = f₂ (f₁ a)} (invf₂ a) (ap f₂ (invg₂ (f₁ a))) }

isoTransport : ∀ {k l} {A : Set k} (B : A → Set l) {x y : A} (p : x ≡ y) → iso (transport B p)
isoTransport B refl = isoId

isoInv : ∀ {k l} {A : Set k} {B : Set l} {f : A → B} (isof : iso f) → iso (iso.inv isof)
isoInv {f = f} record { inv = g ; invLeft = invLeft ; invRight = invRight } 
             = record { inv = f ; invLeft = invRight ; invRight = invLeft }




--Results about Σ and isomorphisms.

Σfun : ∀ {k l m n} {A₁ : Set k} {A₂ : Set l} {B₁ : A₁ → Set m} {B₂ : A₂ → Set n}
       (f : A₁ → A₂) → ({a : A₁} → B₁ a → B₂ (f a))
       → Σ A₁ B₁ → Σ A₂ B₂
Σfun f F (a , b) = (f a , F b)


isoΣfun : ∀ {k l m n} {A₁ : Set k} {A₂ : Set l} {B₁ : A₁ → Set m} {B₂ : A₂ → Set n}
          {f : A₁ → A₂} {F : {a : A₁} → B₁ a → B₂ (f a) }
          → iso f → ((a : A₁) → iso (F {a})) → iso (Σfun {B₂ = B₂} f F)
isoΣfun {B₁ = B₁} {B₂ = B₂} {f} {F} record { inv = g ; invLeft = invLeft ; invRight = invRight } isoF
          = record { inv = λ {(a₂ , b₂) → (g a₂) , (iso.inv (isoF (g a₂)) (transport B₂ (invLeft a₂) b₂))} ;
                     invLeft = λ {(a₂ , b₂) → equalΣ (invLeft a₂) (iso.invLeft (isoF (g a₂)) _) } ;
                     invRight = λ {(a₁ , b₁) → equalΣ (invRight a₁) (≡Trans
                                                 {y = iso.inv (isoF (g (f a₁))) (F (transport B₁ (invRight a₁) b₁))}
                                                 (iso.invRight (isoF (g (f a₁))) _)
                                                 (ap (iso.inv (isoF (g (f a₁))))
                                                 (≡Trans {y = transport B₂ (ap f (invRight a₁)) (F b₁)}
                                                         (transportComp (invRight a₁) F)
                                                         (transportEqualPaths {b = F b₁} 
                                                                  (ap f (invRight a₁)) (invLeft (f a₁)) UIP) )))}}

{-
isoΣAssoc : ∀ {k l m} {A : Set k} {B : A → Set l} {C : Σ A B → Set m} → iso (ΣAssoc A B C)
isoΣAssoc = record { inv = λ {((a , b) , c) → (a , (b , c))} ; 
                     invLeft = λ {((a , b) , c) → refl} ; 
                     invRight = λ {(a , (b , c)) → refl} }
-}

--Results about iso and ∨

iso∨Assoc : ∀ {k l m} {A : Set k} {B : Set l} {C : Set m} → iso (∨Assoc {A = A} {B = B} {C = C})
iso∨Assoc = record { inv = λ { (left a) → left (left a) ; 
                               (right (left b)) → left (right b) ; 
                               (right (right c)) → right c} ; 
                     invLeft = λ { (left a) → refl ; (right (left b)) → refl ; (right (right c)) → refl} ; 
                     invRight = λ { (left (left a)) → refl ; (left (right b)) → refl ; (right c) → refl} }


iso∨Nat : ∀ {k l m n} {A : Set k} {B : Set l} {C : Set m} {D : Set n} {f₁ : A → C} {f₂ : B → D} 
          → iso f₁ → iso f₂ → iso (∨Nat f₁ f₂)
iso∨Nat record { inv = g₁ ; invLeft = invLeft₁ ; invRight = invRight₁ } 
     record { inv = g₂ ; invLeft = invLeft₂ ; invRight = invRight₂ } 
   = record { inv = ∨Nat g₁ g₂ ; 
              invLeft = λ { (left c) → ap left (invLeft₁ c) ; (right d) → ap right (invLeft₂ d)} ; 
              invRight = λ { (left a) → ap left (invRight₁ a) ; (right b) → ap right (invRight₂ b)} }  








--We define injective function

injective : ∀ {k l} {A : Set k} {B : Set l} (f : A → B) → Set (k ⊔ l)
injective {A = A} f = {x y : A} → f x ≡ f y → x ≡ y



--We show Σ and injective interact well
--We use axiom K

injectiveEqual : ∀ {k l m} {A : Set k} {B : Set l} {a₁ a₂ : A} {f : A → B} (C : f a₁ ≡ f a₂ → Set m)
                 → injective f → Σ (a₁ ≡ a₂) (C o ap f) ↔ Σ (f a₁ ≡ f a₂) C
injectiveEqual C injf = (λ {(refl , c) → refl , c}) , 
                        λ {(p , c) → injf p , transport C UIP c}



injectiveIso : ∀ {k l} {A : Set k} {B : Set l} {f : A → B} → iso f → injective f
injectiveIso {f = f} record { inv = g ; invLeft = invLeft ; invRight = invRight } {x} {y} p 
                  = ≡Trans {y = g (f x)} (invRight x) (≡Trans {y = g (f y)} (ap g p) (≡Sym (invRight y)))






--We define pullback

Pullback : ∀ {k l m} {A : Set k} {B : Set l} {C : Set m} (f : A → C) (g : B → C) → Set (k ⊔ l ⊔ m)
Pullback {A = A} {B = B} f g = Σ (A ∧ B) (λ {(a , b) → f a ≡ g b})  


{-
mkPullback : ∀ {k l m} {A : Set k} {B : Set l} {C : Set m} {f : A → C} {g : B → C} (a : A) (b : B) (eq : f a ≡ g b) → Pullback f g
mkPullback a b eq = ((a , b) , eq)
-}
equalPullback : ∀ {k l m} {A : Set k} {B : Set l} {C : Set m} {f : A → C} {g : B → C}
                   {a₁ a₂ : A} {b₁ b₂ : B} {eq₁ : f a₁ ≡ g b₁} {eq₂ : f a₂ ≡ g b₂}
                   → a₁ ≡ a₂ → b₁ ≡ b₂ → Equal (Pullback f g) ((a₁ , b₁) , eq₁) ((a₂ , b₂) , eq₂)
equalPullback refl refl = equalΣ refl UIP





{-
--Properties of ≅


≅Refl : ∀ {k} {A : Set k} → A ≅ A
≅Refl = record { isoFun = Id ; isIso = isoId }

≅Trans : ∀ {k l m} {A : Set k} (B : Set l) {C : Set m} → A ≅ B → B ≅ C → A ≅ C
≅Trans B record { isoFun = f₁ ; isIso = isof₁ } 
           record { isoFun = f₂ ; isIso = isof₂ }
         = record { isoFun = f₂ o f₁ ; isIso = isoComp isof₁ isof₂ }

≅Sym : ∀ {k l} {A : Set k} {B : Set l} → A ≅ B → B ≅ A
≅Sym record { isoFun = f ; 
                isIso = record { inv = g ; 
                                 invLeft = invLeft ; 
                                 invRight = invRight } } 
       = record { isoFun = g ; 
                  isIso = record { inv = f ; 
                                   invLeft = invRight ; 
                                   invRight = invLeft } }

--Results about ∨ and isomorphisms

--∨Flip : 

∨Sym : ∀ {k l} {A : Set k} {B : Set l} 
       → A ∨ B ≅ B ∨ A
∨Sym = record { isoFun = λ { (left a) → right a ; (right b) → left b} ; 
                isIso = record { inv = λ { (left b) → right b ; (right a) → left a} ; 
                                 invLeft = λ { (left b) → refl ; (right a) → refl} ; 
                                 invRight = λ { (left a) → refl ; (right b) → refl} } }

∨Assoc : ∀ {k l m} {A : Set k} {B : Set l} {C : Set m} 
         → A ∨ (B ∨ C) ≅ (A ∨ B) ∨ C
∨Assoc = record { isoFun = λ { (left a) → left (left a) ; (right (left b)) → left (right b) ; (right (right c)) → right c} ; 
                  isIso = record { inv = λ { (left (left a)) → left a ; (left (right b)) → right (left b) ; (right c) → right (right c)} ; 
                                   invLeft = λ { (left (left a)) → refl ; (left (right b)) → refl ; (right c) → refl} ; 
                                   invRight = λ { (left a) → refl ; (right (left b)) → refl ; (right (right c)) → refl} } }

iso∨ : ∀ {k l m n} {A₁ : Set k} {A₂ : Set l} {B₁ : Set m} {B₂ : Set n} 
       → A₁ ≅ A₂ → B₁ ≅ B₂ → A₁ ∨ B₁ ≅ A₂ ∨ B₂
iso∨ record { isoFun = f₁ ;
              isIso = record { inv = g₁ ;
                               invLeft = invLeft₁ ;
                               invRight = invRight₁ } }
     record { isoFun = f₂ ;
              isIso = record { inv = g₂ ;
                               invLeft = invLeft₂ ;
                               invRight = invRight₂ } } 
     = record { isoFun = λ { (left a₁) → left (f₁ a₁) ; (right b₁) → right (f₂ b₁)} ; 
                isIso = record { inv = λ { (left a₂) → left (g₁ a₂) ; (right b₂) → right (g₂ b₂)} ; 
                                 invLeft = λ { (left a₂) → ap left (invLeft₁ a₂) ; (right b₂) → ap right (invLeft₂ b₂)} ; 
                                 invRight = λ { (left a₁) → ap left (invRight₁ a₁) ; (right b₁) → ap right (invRight₂ b₁)} } }


--Results about ⊤ and isomorphism

iso⊤ : ∀ {k} {A : Set k} (y : A) → ((x : A) → x ≡ y) → A ≅ ⊤
iso⊤ = λ y f → record { isoFun = λ _ → * ; 
                        isIso = record { inv = λ _ → y ; 
                                         invLeft = λ { * → refl} ; 
                                         invRight = f } }


--Results about ⊥ and isomorphism
--QUESTION : Am I forced to use efql ?

iso⊥ : ∀ {k l} {A : Set k} {B : Set l} → (A → ⊥) → (B → ⊥) → A ≅ B
iso⊥ A⊥ B⊥ = record { isoFun = λ a → efql (A⊥ a) ; 
                      isIso = record { inv = λ b → efql (B⊥ b) ; 
                                       invLeft = λ b → efql (B⊥ b) ; 
                                       invRight = λ a → efql (A⊥ a) } }

iso∨⊥left : ∀ {k l} {A : Set k} {B : Set l} → (A → ⊥) → B ≅ A ∨ B
iso∨⊥left A⊥ = record { isoFun = right ; 
                    isIso = record { inv = λ { (left a) → efql (A⊥ a) ; (right b) → b} ; 
                                     invLeft = λ { (left a) → efql (A⊥ a) ; (right b) → refl} ; 
                                     invRight = λ b → refl } }  

iso∨⊥right : ∀ {k l} {A : Set k} {B : Set l} → (B → ⊥) → A ≅ A ∨ B
iso∨⊥right {A = A} {B = B} B⊥ = ≅Trans (B ∨ A) (iso∨⊥left B⊥) ∨Sym 
-}



