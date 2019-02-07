{-# OPTIONS --allow-unsolved-metas #-}

module HomotopyProposition where

open import Data
open import Agda.Primitive
open import FibrantUniverse





--We give definition of dependent paths


DepPath : ∀ {k l} {X : Set k} (P : X → Set l) {x y : X} (p : x ~~> y) → (tx : P x) (ty : P y) → Set l
DepPath P [ p , refl , refl ] tx ty = dPath (P o p) tx ty


_$$_ : ∀ {k l} {X : Set k} {P : X → Set l} {x y : X} {p : x ~~> y} {tx : P x} {ty : P y} → DepPath P p tx ty → (i : I) → P (p $ i)
_$$_ = {!!}

--$$Constant : ∀ {k l} {X : Set k} {Y : Set l} {x y : X} {p : x ~~> y} {tx : P x}

--We define homotopy proposition

hProp : ∀ {k} (X : Set k) → Set k
hProp X = (x y : X) → x ~~> y

hPropPredicate : ∀ {k l} {X : Set k} (P : X → Set l) → Set (k ⊔ l)
hPropPredicate {X = X} P = {x y : X} (p : x ~~> y) (tx : P x) (ty : P y) → DepPath P p tx ty

hPropPredicateConstant : ∀ {k l} {X : Set k} {Y : Set l} → hProp Y → hPropPredicate (λ (_ : X) → Y)
hPropPredicateConstant hPropY [ p , refl , refl ] tx ty = hPropY tx ty

hProp→ : ∀ {k l} {X : Set k} {P : X → Set l} → ({x : X} → hProp (P x)) → hProp ((x : X) → P x)
hProp→ hyp f g = [ (λ i x → (hyp (f x) (g x)) $ i  ) ,
                   funext (λ x → eqe₀ (hyp (f x) (g x))) ,
                   funext (λ x → eqe₁ (hyp (f x) (g x))) ]

{-
hPropImp→ : ∀ {k l} {X : Set k} {P : X → Set l} → ({x : X} → hProp (P x)) → hProp ({x : X} → P x)
hPropImp→ hyp f g = [ (λ i {x} → (hyp (f {x}) (g {x})) $ i) ,
                      {!!} ,
                      {!!} ]
-}


hPropSingleton : ∀ {k l} {X : Set k} {P : X → Set l} → ((x : X) → isProp (P x)) → ()hPropPredicate P
hPropSingleton = {!!}
