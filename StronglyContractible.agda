{-# OPTIONS --allow-unsolved-metas #-}

module StronglyContractible where

open import Agda.Primitive
open import Data
open import FibrantUniverse
open import Cofibration

module _ {k l} {X : Set k} {Y : Set l} (f : X → Y) where

  Section : Set (k ⊔ l)
  Section = (y : Y) → fibre f y

StronglyContractible : ∀ {k l} {X : Set k} {Y : Set l} (f : X → Y) → Set (k ⊔ l)
StronglyContractible f = {k : ℕ} → Section (< border k / f >)


StronglyContractiblePullback : ∀ {k l m} {X : Set k} {Y : Set l} {Z : Set m} {f : X → Z} {g : Y → Z}
                               → StronglyContractible g → StronglyContractible (Pullback.proj₁ {f = f} {g = g})
StronglyContractiblePullback = {!!}

StronglyContractibleTrivialFibration : ∀ {k l} {X : Set k} {Y : Set l} {f : X → Y}
                                       → TrivialFibrationBasis f → StronglyContractible f
StronglyContractibleTrivialFibration = {!!}
