module Monoid where

open import Agda.Primitive
open import Data
open import FibrantUniverse
open import StronglyContractible
open import FiniteSet
open import Operad



StronglyContractibleOp : ∀ {k l} {P : (A : Set) → {{_ : FOSet A}} → Set k}
                                    {Q : (A : Set) → {{_ : FOSet A}} → Set l}
                                    (α : (A : Set) → {{_ : FOSet A}} → P A → Q A)
                                    → Set (lsuc lzero ⊔ k ⊔ l)

StronglyContractibleOp α = (A : Set) → {{_ : FOSet A}} → StronglyContractible (α A)


record SectionOp {k l} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
                       {Q : (A : Set) → {{_ : FOSet A}} → Set l} {{_ : Operad Q}}
                       (α : (A : Set) → {{_ : FOSet A}} → P A → Q A) : Set (lsuc lzero ⊔ k ⊔ l) where
       field
         map : (A : Set) {{_ : FOSet A}} → Q A → P A
         isMorphism : HomOperad map
         isSection : (A : Set) {{_ : FOSet A}} → (c : Q A) → α A (map A c) ≡ c 



postulate
  ∞Mon : (A : Set) → {{_ : FOSet A}} → Set

  instance
    ∞MonOp : Operad ∞Mon

  ∞MonSection : ∀ {k} {P : (A : Set) → {{_ : FOSet A}} → Set k} {{_ : Operad P}}
                {β : (A : Set) → {{_ : FOSet A}} → P A → ∞Mon A} (homβ : HomOperad β)
                → StronglyContractibleOp β → SectionOp β
