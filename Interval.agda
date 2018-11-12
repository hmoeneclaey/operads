--This module will contains the fibrant universes and their homotopical structure. 

module Interval where

open import Data


postulate
  I : Set
  e₁ e₂ : I
  inf : I ∧ I → I