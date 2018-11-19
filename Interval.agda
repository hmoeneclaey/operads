--This module will contains the fibrant universes and their homotopical structure. 

module Interval where

open import Data


postulate
  I : Set
  e₀ e₁ : I
  _⊔_ : I → I → I


postulate Fib : ∀ {k} → Set k → Set k

 
instance
  postulate
    ΠFib : ∀ {k l} → {A : Set k} → {{_ : Fib A}} → {B : A → Set l} → {{_ : {a : A} → Fib (B a)}} → Fib ((a : A) → B a)


module testing where

  testFibrant : ∀ {k} (A : Set k) {{_ : Fib A}} → Fib A
  testFibrant A {{Afib}} = Afib


  module _ {k l} {A : Set k} {{_ : Fib A}} {B : A → Set l} {{_ : {a : A} → Fib (B a)}} where
    test = testFibrant ((a : A) → B a)
    test3 = λ (a : A) → testFibrant (B a)


  module _ {k l m} {A : Set k} {{_ : Fib A}} {B : A → Set l} {{_ : {a : A} → Fib (B a)}} {C : Σ A B → Set m} {{_ : {x : Σ A B} → Fib (C x)}} where
    test2 = testFibrant ((a : A) → (b : B a) → C (a , b))
