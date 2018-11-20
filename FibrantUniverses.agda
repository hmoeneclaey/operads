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
    deq₁ : dpath e₀ ≡ x
    deq₂ : dpath e₁ ≡ y


postulate
  Fib : ∀ {k} → Set k → Set k

  instance
    ⊤Fib : Fib ⊤
  
    ΠFib : ∀ {k l} {A : Set k} {{_ : Fib A}} {B : A → Set l} {{_ : {a : A} → Fib (B a)}}
           → Fib ((a : A) → B a)
         
    ΣFib : ∀ {k l} {A : Set k} {{_ : Fib A}} {B : A → Set l} {{_ : {a : A} → Fib (B a)}}
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





--Now we give definitions

Path : ∀ {k} (X : Set k) (x y : X) → Set k
Path X x y = dPath (λ _ → X) x y

record Contr {k} (X : Set k) : Set k where
  field
    center : X
    isContr : (y : X) → Path X center y


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




--A bunch of postulate which will be proven latter
postulate
  instance
    fibFiniteProf : ∀ {k} {A : Set} {{_ : FOSet A}} {X : Set k} {{_ : Fib X}} → Fib (A → X)

postulate
  ≅Contr : ∀ {k l} {X : Set k} {Y : Set l} → X ≅ Y → Contr X → Contr Y

postulate
  ΠContr : ∀ {k l} {X : Set k} {P : X → Set l} → ((x : X) → Contr (P x)) → Contr ((x : X) → P x)
