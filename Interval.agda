--This module will contains the fibrant universes and their homotopical structure. 

module Interval where

open import Data


postulate
  I : Set
  e₀ e₁ : I
  inf : I ∧ I → I