module MainTheorem where

open import Agda.Primitive
open import Data
open import FiniteSet
open import Operad
open import FibrantUniverse
open import HomotopyTransfer
open import ContractibleSectionOperad


--We list unwanted postulates
--LoopSpace l.336

--We list allow-unsolve-meta
--LimitOperad


postulate
  ∞Mon : (A : Set) → {{_ : FOSet A}} → Set
  instance
    Op∞Mon : Operad ∞Mon
  ∞MonSection : sectionStronglyContractibleMapOp ∞Mon



--We introduce some notations

Ω : ∀ {k} (X : Set k) → X → Set k
Ω X x = x ~~> x

_≃_ : ∀ {k l} (X : Set k) (Y : Set l) → Set (k ⊔ l)
X ≃ Y = Σ (X → Y) (λ f → Equiv f)



--We give the main theorems

mainTheorem1 : ∀ {k l} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}}
               → X ≃ Y → Algebra ∞Mon Y → Algebra ∞Mon X

mainTheorem1 (f , equivf) algY = algebraInvariantEquiv (Cofib∞Mon ∞MonSection) equivf algY


mainTheorem2 : ∀ {k} {X : Set k} {{_ : Fib X}} {x : X}
               → Algebra ∞Mon (Ω X x)

mainTheorem2 = ActLoopSpace∞Mon ∞MonSection
