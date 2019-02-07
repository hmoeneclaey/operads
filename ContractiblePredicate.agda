{-# OPTIONS --allow-unsolved-metas #-}

module ContractiblePredicate where

open import Data
open import Agda.Primitive
open import FibrantUniverse





--We give definition of dependent paths


DepPath : ∀ {k l} {X : Set k} (P : X → Set l) {x y : X} (p : x ~~> y) → (tx : P x) (ty : P y) → Set l
DepPath P [ p , refl , refl ] tx ty = dPath (P o p) tx ty



hProp : ∀ {k} (X : Set k) → Set k
hProp X = {x y : X} → x ~~> y

hPropPredicate : ∀ {k l} {X : Set k} (P : X → Set l) → Set (k ⊔ l)
hPropPredicate {X = X} P = {x y : X} {p : x ~~> y} {tx : P x} {ty : P y} → DepPath P p tx ty



hPropPredicateConstant : ∀ {k l} {X : Set k} {Y : Set l} → hProp Y → hPropPredicate (λ (_ : X) → Y)
hPropPredicateConstant = {!!}
