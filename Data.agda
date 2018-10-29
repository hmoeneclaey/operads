module Data where

open import Agda.Primitive



--Composition and identity

--Is it useful ?
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




--Natural numbers

data ℕ : Set where
  O : ℕ
  s : ℕ → ℕ



--Equality

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

transportEqualPaths : ∀ {k l} {A : Set k} {B : A → Set l} {x y : A} {b : B x}
                      {p q : x ≡ y} {b : B x} 
                      → p ≡ q → transport B p b ≡ transport B q b
transportEqualPaths refl = refl



--Results about Σ and equality

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

isoId : ∀ {k} {A : Set k} → iso (λ (x : A) → x)
isoId = record { inv = Id ; invLeft = λ b → refl ; invRight = λ a → refl }

isoEq : ∀ {k} {A : Set k} → A ≅ A
isoEq = record { isoFun = Id ; isIso = isoId }






--Some results about Σ, isomorphisms and equalities, needed to do the Σ of finite sets.

isoΣfibre : ∀ {k l m} {A : Set k} {B₁ : A → Set l} {B₂ : A → Set m} (isoB : (a : A) → B₁ a ≅ B₂ a ) → Σ A B₁ ≅ Σ A B₂
isoΣfibre isoB = record { isoFun = λ {(a , b₁) → a , (_≅_.isoFun (isoB a) b₁)} ; 
                          isIso = record { inv = λ {(a , b₂) → a , iso.inv (_≅_.isIso (isoB a)) b₂} ; 
                                           invLeft = λ {(a , b₂) → equalΣfibre (iso.invLeft (_≅_.isIso (isoB a)) b₂)} ; 
                                           invRight = λ {(a , b₁) → equalΣfibre (iso.invRight (_≅_.isIso (isoB a)) b₁)} 
                                         } 
                        }

isoΣbase : ∀ {k l m} {A₁ : Set k} {A₂ : Set l} {B : A₂ → Set m} 
           (f : A₁ → A₂) → iso f → Σ A₁ (B o f) ≅ Σ A₂ B
isoΣbase {B = B} f record { inv = g ; invLeft = invLeft ; invRight = invRight } = 
         record { isoFun = λ {(a₁ , b) → (f a₁) , b} ; 
                  isIso = record { inv = λ {(a₂ , b) → g a₂ , transport B (invLeft a₂) b} ; 
                                   invLeft = λ {(a₂ , b) → equalΣ (invLeft a₂) refl} ; 
                                   invRight = λ {(a₁ , b) → equalΣ (invRight a₁) 
                                            ( equalTrans (transport B (ap f (invRight a₁)) b) 
                                              ( transportComp (invRight a₁)) 
                                              ( transportEqualPaths {b = b} {p = ap f (invRight a₁)} {q = invLeft (f a₁)} UIP  ))}
                                 }
                }

