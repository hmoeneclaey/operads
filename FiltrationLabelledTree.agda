{-# OPTIONS --rewriting #-}

module FiltrationLabelledTree where


open import Data
open import LabelledTree
open import RewritingLabelledTree
open import QuotientLabelledTree
open import AltOperad
open import FibrantUniverse
open import Cofibration



--First some things about ≤ on ℕ

ordℕ : ℕ → ℕ → Set
ordℕ = {!!}

_⊂_ : ℕ → ℕ → Set
m ⊂ n = (m ≡ n) ∨ ordℕ m n



--We define trees with at most k internal vertices

record ≤Ltree (k : ℕ) (n : ℕ) : Set where
  field
    tree : Ltree n
    size : cardinalInternalVertice tree ⊂ k

incLtree : {k n : ℕ} → ≤Ltree (pred k) n → ≤Ltree k n
incLtree record { tree = t ; size = eq } = record { tree = t ; size = {!!} }

LtreeTo≤Ltree : {n : ℕ} (t : Ltree n) → ≤Ltree (cardinalInternalVertice t) n
LtreeTo≤Ltree t = record { tree = t ; size = left refl }

≤LtreeToLtree : {k n : ℕ} (t : ≤Ltree k n) → Ltree n
≤LtreeToLtree = ≤Ltree.tree

data _⇒₂_ : {k n : ℕ} → ≤Ltree k n → ≤Ltree (pred k) n → Set where
  mk⇒₂ : {n : ℕ} {t₁ t₂ : Ltree n} → t₁ ⇒ t₂ → LtreeTo≤Ltree t₁ ⇒₂ record { tree = t₂ ; size = {!!} }
--record { tree = t₁ ; size = _ } ⇒₂ record { tree = t₂ ; size = _ } = t₁ ⇒ t₂

⊥Ltree₂ : {k n : ℕ} → (t : ≤Ltree k n) (a : InternalVertice (≤LtreeToLtree t)) → ≤Ltree (pred k) (cardinal⊥Ltree a)
⊥Ltree₂ record { tree = t ; size = _ } a = record { tree = ⊥Ltree a ; size = {!!} }

⊤Ltree₂ : {k n : ℕ} → (t : ≤Ltree k n) (a : InternalVertice (≤LtreeToLtree t)) → ≤Ltree (pred k) (cardinal⊤Ltree a)
⊤Ltree₂ record { tree = t ; size = _ } a = record { tree = ⊤Ltree a ; size = {!!} }



--Morphism build using filtration

module _ {k} {P : ℕ → Set k} {{_ : AltOperad P}}
         (α : {k n : ℕ} → ≤Ltree k n → P n)
         (αinc : {k n : ℕ} → {t : ≤Ltree k n} → α t ≡ α {s k} (incLtree t))
         (αid : α (LtreeTo≤Ltree idLtree) ≡ idAlt)
         (αγ : {k n : ℕ} {t : ≤Ltree k n} (a : InternalVertice (≤LtreeToLtree t)) → EvalLtree a ≡ e₁
         → α t ≡ transport P (≡cardinal⊥⊤Ltree {k = a}) (γAlt (α (⊥Ltree₂ t a)) (leaf⊥Ltree a) (α (⊤Ltree₂ t a))))
         where

       ≡αLtree : {n k₁ k₂ : ℕ} {t₁ : ≤Ltree k₁ n} {t₂ : ≤Ltree k₂ n}
                 → ≤LtreeToLtree t₁ ≡ ≤LtreeToLtree t₂ → α t₁ ≡ α t₂ 
       ≡αLtree = {!!}

       MapFiltrationAux : {n : ℕ} → Ltree n → P n
       MapFiltrationAux = α o LtreeTo≤Ltree

       HomAltOpFiltrationAux : HomAltOperad {{OpLtree}} MapFiltrationAux
       HomAltOpFiltrationAux = record { HomIdAlt = αid ;
                                        HomγAlt = {!!} }

       module _  (α⇒ : {k n : ℕ} {t₁ : ≤Ltree k n} {t₂ : ≤Ltree (pred k) n} → t₁ ⇒₂ t₂ → α t₁ ≡ α t₂) where

         MapFiltration : {n : ℕ} → Qtree n → P n 
         MapFiltration = QtreeRec MapFiltrationAux (λ r → ≡Trans (α⇒ (mk⇒₂ r)) (≡αLtree refl))

         HomAltOpFiltration : HomAltOperad {{OpQtree}} MapFiltration
         HomAltOpFiltration = QtreeRecOperad HomAltOpFiltrationAux

         module _ {β : {n : ℕ} → P n → Qtree n}
                  (αsec : {k n : ℕ} {t : ≤Ltree k n} → β (α t) ≡ [ ≤LtreeToLtree t ]) where

           SectionFiltration : {n : ℕ} (t : Qtree n) → β (MapFiltration t) ≡ t
           SectionFiltration = QtreeProp (λ _ → αsec) UIP




module _ {l} {P : ℕ → Set l} {{_ : AltOperad P}}
         {β : {n : ℕ} → P n → Qtree n} where

       record PartialMorphism (k : ℕ) (morphism₂ : {n : ℕ} → ≤Ltree (pred k) n → P n) : Set l where
         field
--           morphism₂ : {n : ℕ} → ≤Ltree (pred k) n → P n
           morphism₁ : {n : ℕ} → ≤Ltree k n → P n
           inclusion : {n : ℕ} {t : ≤Ltree (pred k) n} → morphism₁ (incLtree t) ≡ morphism₂ t
           section : {n : ℕ} {t : ≤Ltree k n} → β (morphism₁ t) ≡ [ ≤LtreeToLtree t ]
           reduction : {n : ℕ} {t₁ : ≤Ltree k n} {t₂ : ≤Ltree (pred k) n} → t₁ ⇒₂ t₂ → morphism₁ t₁ ≡ morphism₂ t₂
           composition : {n : ℕ} {t : ≤Ltree k n} (a : InternalVertice (≤LtreeToLtree t)) → EvalLtree a ≡ e₁
                         → morphism₁ t ≡ transport P (≡cardinal⊥⊤Ltree {k = a})
                                        (γAlt (morphism₂ (⊥Ltree₂ t a)) (leaf⊥Ltree a) (morphism₂ (⊤Ltree₂ t a)))

       module _ (contrβ : {n : ℕ} → StronglyContractibleMap (β {n})) where

         

--       module
       

       --(contrβ : {n : ℕ} → StronglyContractibleMap (β {n}))
