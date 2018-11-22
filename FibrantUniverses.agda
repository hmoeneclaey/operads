{-# OPTIONS --rewriting #-}


--This module will contains the fibrant universes and their homotopical structure. 

module FibrantUniverses where


open import Data
open import Agda.Primitive
open import FiniteSet


postulate _↦_ : ∀ {i} {A : Set i} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}




--Here we write every postulate for the fibrant universes
--Q : Fib Set k → Set is okay ?

postulate
  I : Set
  e₀ e₁ : I


record dPath {k} (P : I → Set k) (x : P e₀) (y : P e₁) : Set k where
  constructor [_,_,_]
  field
    dpath : (i : I) → P i
    deq₀ : dpath e₀ ≡ x
    deq₁ : dpath e₁ ≡ y


postulate
  Fib : ∀ {k} → Set k → Set k

  instance
    ⊤Fib : ∀ {k} → Fib (⊤ {k})
  
    ΠFib : ∀ {k l} {A : Set k} {{_ : Fib A}} {B : A → Set l} {{_ : {a : A} → Fib (B a)}}
           → Fib ((a : A) → B a)
         
    ΣFib : ∀ {k l} {A : Set k} {{_ : Fib A}} {B : A → Set l} {{fibB : {a : A} → Fib (B a)}}
           → Fib (Σ A B)
         
    IFib : ∀ {k} {P : I → Set k} {{_ : (i : I) → Fib (P i)}} {x : P e₀} {y : P e₁}
           → Fib (dPath P x y)

  ≅Fib : ∀ {k l} {X : Set k} {Y : Set l} → X ≅ Y → {{_ : Fib X}} → Fib Y

module _ {k l} {X : Set k} {{_ : Fib X}} 
  (C : (I → X) → Set l) {{_ : (p : I → X) → Fib (C p)}} 
  (d : (x : X) → C (λ i → x)) where
  postulate
    J : (p : I → X) → C p
    Jcompute : (x : X) → J (λ i → x) ↦ d x
    {-# REWRITE Jcompute #-}





--Now we give definition of paths

Path : ∀ {k} (X : Set k) (x y : X) → Set k
Path X x y = dPath (λ _ → X) x y

_$_ : ∀ {k} {P : I → Set k} {x : P e₀} {y : P e₁} → dPath P x y → (i : I) → P i
p $ i = (dPath.dpath p) i

infix 35 _$_

eqe₀ : ∀ {k} {P : I → Set k} {x : P e₀} {y : P e₁} (p : dPath P x y) → p $ e₀ ≡ x
eqe₀ p = dPath.deq₀ p

eqe₁ : ∀ {k} {P : I → Set k} {x : P e₀} {y : P e₁} (p : dPath P x y) → p $ e₁ ≡ y
eqe₁ p = dPath.deq₁ p






record Contr {k} (X : Set k) : Set k where
  field
    center : X
    isContr : (y : X) → Path X center y


--Properties of maps

module _ {k l} {X : Set k} {Y : Set l} (f : X → Y) where

  record fibre (y : Y) : Set (k ⊔ l) where
    constructor _,_
    field
      point : X
      equal : f point ≡ y

  Fibration : Set (k ⊔ l)
  Fibration = {y : Y} → Fib (fibre y)

  ContrMap : Set (k ⊔ l)
  ContrMap = {y : Y} → Contr (fibre y)

  record TrivialFibration : Set (k ⊔ l) where
    field
      isFib : Fibration
      isContr : ContrMap

  record Equiv : Set (k ⊔ l) where
    field
      inv₁ : Y → X
      invLeft : (y : Y) → Path Y y (f (inv₁ y))
      inv₂ : Y → X
      invRight : (x : X) → Path X x (inv₂ (f x))





--Results about fibrancy

finiteProdFib : ∀ {k} {X : Set k} {{_ : Fib X}} {n : ℕ} → Fib (Prod X n)
finiteProdFib {n = O} = ⊤Fib
finiteProdFib {n = s n} = ΣFib {{fibB = finiteProdFib}}

fibFiniteCanonical : ∀ {n : ℕ} {k} {X : Set k} {{_ : Fib X}} → Fib (Fin n → X)
fibFiniteCanonical {n} {X = X} = ≅Fib {X = Prod X n}
                                      (record { isoFun = prodFun ; isIso = isoProdFun })
                                      {{finiteProdFib}}

instance
  FiniteCofib : ∀ {k} {A : Set} {{_ : FOSet A}} {X : Set k} {{_ : Fib X}} → Fib (A → X)
  FiniteCofib {{ record { cardinal = card ; funFO = f ; isIsoFO = isof } }} {X} =
                ≅Fib {X = Fin card → X}
                     (record { isoFun = preComp f ;
                               isIso = isoPreComp isof })
                     {{fibFiniteCanonical}}


totalSpaceFib : ∀ {k l} {X : Set k} {Y : Set l} {p : X → Y} {{_ : Fibration p}} → {{_ : Fib Y}} → Fib X
totalSpaceFib {Y = Y} {p = p} = ≅Fib {X = Σ Y (λ y → fibre p y)}
                                     (record { isoFun = λ {(y , (x , eq)) → x} ;
                                               isIso = record { inv = λ x → (p x) , (x , refl) ;
                                                                invLeft = λ _ → refl ;
                                                                invRight = λ {(y , (x , refl)) → refl} } })




--Results about contractibility


≅Contr : ∀ {k l} {X : Set k} {Y : Set l} → X ≅ Y → Contr X → Contr Y

≅Contr record { isoFun = f ;
                isIso = record { inv = g ;
                                 invLeft = invLeft ;
                                 invRight = _ } }
       record { center = x ;
                isContr = contrX }
     = record { center = f x ;
                isContr = λ y → let p = contrX (g y) in
                                [ (λ i → f (p $ i)) ,
                                  (ap f (eqe₀ p)) ,
                                  ≡Trans (ap f (eqe₁ p)) (≡Sym (invLeft y)) ] }


ΠContr : ∀ {k l} {X : Set k} {P : X → Set l} → ((x : X) → Contr (P x)) → Contr ((x : X) → P x)

ΠContr contrP = record { center = λ x → Contr.center (contrP x) ;
                         isContr = λ f → let p = λ x → Contr.isContr (contrP x) (f x) in
                                     [ (λ i x → (p x) $ i) ,
                                       funext (λ x → eqe₀ (p x)) ,
                                       funext (λ x → eqe₁ (p x)) ] } 
