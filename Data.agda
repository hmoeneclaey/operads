module Data where

open import Agda.Primitive



--Composition and identity

Id : ∀ {k} {A : Set k} → A → A
Id x = x

_o_ : ∀ {k l m} {A : Set k} {B : A → Set l} {C : {a : A} → B a → Set m} 
      → (g : {a : A} → (b : B a) → C b) 
      → (f : (a : A) → B a) 
      → (a : A) → C (f a)
g o f = λ a → g (f a)




--Logical connectives

data ⊥ : Set where

data ⊤ : Set where
  * : ⊤

data Σ {k l} (A : Set k) (B : A → Set l) : Set (k ⊔ l)  where
  _,_ : (a : A) → B a → Σ A B

--infixr 56 _,_

_∧_ : ∀ {k l} → Set k → Set l → Set (k ⊔ l)
A ∧ B = Σ A (λ _ → B)

data _∨_ {k l} (A : Set k) (B : Set l) : Set (k ⊔ l) where
  left : A → A ∨ B
  right : B → A ∨ B

infix 36 _∨_

_↔_ : ∀ {k l} (A : Set l) (B : Set k) → Set (k ⊔ l)
A ↔ B = (A → B) ∧ (B → A)

infix 46 _↔_


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

--For now we postulate UIP, although Axiom K is perhaps a bit better
postulate UIP : ∀ {k} {A : Set k} {x y : A} {p q : x ≡ y} → p ≡ q

--When we need to declare the type explicitly
--I should ask guillaume for a neater solution
Eq : ∀ {k} (A : Set k) → A → A → Set k
Eq A x y = x ≡ y



--Basic structure for strict equality

transport : ∀ {k l} {A : Set k} (B : A → Set l) {x y : A} → x ≡ y → B x → B y
transport B refl x = x

ap : ∀ {k l} {A : Set k} {B : Set l} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl 

equalSym : ∀ {k} {A : Set k} {x y : A} → x ≡ y → y ≡ x
equalSym refl = refl

equalTrans : ∀ {k} {A : Set k} {x z : A} (y : A) → x ≡ y → y ≡ z → x ≡ z
equalTrans y refl p = p

transportComp : ∀ {k l m} {A₁ : Set k} {A₂ : Set l} {f : A₁ → A₂} {B : A₂ → Set m} {x y : A₁} {b : B (f x)} 
                (p : x ≡ y) → transport (B o f) p b ≡ transport B (ap f p) b 
transportComp refl = refl

transportEqualPaths : ∀ {k l} {A : Set k} {B : A → Set l} {x y : A} {b : B x} {p q : x ≡ y} {b : B x} 
                      → p ≡ q → transport B p b ≡ transport B q b
transportEqualPaths refl = refl



--Results about Σ and equality

--QUESTION : is Eq necessary

equalΣfibre : ∀ {k l} {A : Set k} {B : A → Set l} {a : A} {b₁ b₂ : B a} → b₁ ≡ b₂ → Eq (Σ A B) (a , b₁) (a , b₂)
equalΣfibre refl = refl

equalΣ : ∀ {k l} {A : Set k} {B : A → Set l} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} 
         (p : a₁ ≡ a₂) → transport B p b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂) 
equalΣ refl refl = refl



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

isoRefl : ∀ {k} {A : Set k} → A ≅ A
isoRefl = record { isoFun = Id ; isIso = isoId }

isoComp : ∀ {k l m} {A : Set k} {B : Set l} {C : Set m} 
          {f : A → B} {g : B → C} → iso f → iso g → iso (g o f)
isoComp {f = f₁} {g = g₁} record { inv = f₂ ; invLeft = invf₁ ; invRight = invf₂ } 
                          record { inv = g₂ ; invLeft = invg₁ ; invRight = invg₂ } 
        = record { inv = f₂ o g₂ ; 
                 invLeft = λ b → equalTrans (g₁ (g₂ b)) (invg₁ b) (ap g₁ (invf₁ (g₂ b))) ; 
                 invRight = λ a → equalTrans (f₂ (f₁ a)) (invf₂ a) (ap f₂ (invg₂ (f₁ a))) }

isoTrans : ∀ {k l m} {A : Set k} (B : Set l) {C : Set m} → A ≅ B → B ≅ C → A ≅ C
isoTrans B record { isoFun = f₁ ; isIso = isof₁ } 
           record { isoFun = f₂ ; isIso = isof₂ }
         = record { isoFun = f₂ o f₁ ; isIso = isoComp isof₁ isof₂ }

isoSym : ∀ {k l} {A : Set k} {B : Set l} → A ≅ B → B ≅ A
isoSym record { isoFun = f ; 
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
efql : ∀ {k} {A : Set k} → ⊥ → A
efql () 

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
iso∨⊥right {A = A} {B = B} B⊥ = isoTrans (B ∨ A) (iso∨⊥left B⊥) ∨Sym 



--Results about Σ and isomorphisms.

Σfun : ∀ {k l m n} {A₁ : Set k} {A₂ : Set l} {B₁ : A₁ → Set m} (B₂ : A₂ → Set n) 
       (f : A₁ → A₂) → ((a : A₁) → B₁ a → B₂ (f a))
       → Σ A₁ B₁ → Σ A₂ B₂
Σfun _ f F (a , b) = (f a , F _ b)

isoΣfibre : ∀ {k l m} {A : Set k} {B₁ : A → Set l} {B₂ : A → Set m} 
            (isoB : (a : A) → B₁ a ≅ B₂ a ) → Σ A B₁ ≅ Σ A B₂
isoΣfibre isoB = record { isoFun = λ {(a , b₁) → a , (_≅_.isoFun (isoB a) b₁)} ; 
                          isIso = record { inv = λ {(a , b₂) → a , iso.inv (_≅_.isIso (isoB a)) b₂} ; 
                                           invLeft = λ {(a , b₂) → equalΣfibre (iso.invLeft (_≅_.isIso (isoB a)) b₂)} ; 
                                           invRight = λ {(a , b₁) → equalΣfibre (iso.invRight (_≅_.isIso (isoB a)) b₁)} } }

isoΣbase : ∀ {k l m} {A₁ : Set k} {A₂ : Set l} {B : A₂ → Set m} 
           (f : A₁ → A₂) → iso f → Σ A₁ (B o f) ≅ Σ A₂ B
isoΣbase {B = B} f record { inv = g ; invLeft = invLeft ; invRight = invRight } = 
         record { isoFun = λ {(a₁ , b) → (f a₁) , b} ; 
                  isIso = record { inv = λ {(a₂ , b) → g a₂ , transport B (invLeft a₂) b} ; 
                                   invLeft = λ {(a₂ , b) → equalΣ (invLeft a₂) refl} ; 
                                   invRight = λ {(a₁ , b) → equalΣ (invRight a₁) 
                                            ( equalTrans (transport B (ap f (invRight a₁)) b) 
                                              ( transportComp (invRight a₁)) 
                                              ( transportEqualPaths {b = b} {p = ap f (invRight a₁)} {q = invLeft (f a₁)} UIP  )) } } }

isoΣfun : ∀ {k l m n} {A₁ : Set k} {A₂ : Set l} {B₁ : A₁ → Set m} {B₂ : A₂ → Set n}
          (f : A₁ → A₂) (F : (a : A₁) → B₁ a → B₂ (f a) ) → iso f → ((a : A₁) → iso (F a))
          → iso (Σfun B₂ f F)
isoΣfun f F isof isoF = {!!}