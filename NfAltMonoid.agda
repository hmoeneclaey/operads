{-# OPTIONS --rewriting #-}

module NfAltMonoid where

open import Data
open import FiniteSet
open import NfAltOperad
open import FibrantUniverse
open import HomotopyProposition





--First we define trees

data Tree : ℕ → Set where
  • : Tree O
  ∅ : Tree (s O)
  cons : {m n : ℕ} → Tree m → Tree n → Tree (m + n)



--We define the operad structure on trees

idTree : Tree (s O)
idTree = ∅


γTree : {m n : ℕ} (k : Fin (s m)) → Tree (s m) → Tree n → Tree (m + n)
γTree = {!!}

instance
  NfAltOperadTree : NfAltOperad Tree
  NfAltOperadTree = record
                   { id = idTree
                   ; γ = γTree
                   ; UnitLeft = {!!}
                   ; UnitRight = {!!}
                   ; Assoc₁ = {!!}
                   ; Assoc₂ = {!!}
                   }






--now we define quotiented trees

postulate
  QTree : ℕ → Set
  [_] : {n : ℕ} → Tree n → QTree n 
  trunc : {n : ℕ} → (x y : QTree n) → x ~~> y


module _ {k} {n : ℕ} {P : QTree n → Set k} (d : (t : Tree n) → P [ t ])
         (hPropP : {x y : QTree n} → (tx : P x) (ty : P y) → DepPath P (trunc x y) tx ty) where
       postulate
         QTreeElimTrue : (t : QTree n) → P t
         QTreeElimCompute : (t : Tree n) → QTreeElimTrue [ t ] ↦ d t
         {-# REWRITE QTreeElimCompute #-}
         QTreeElimComputePath : (x y : QTree n) (i : I) → QTreeElimTrue (trunc x y $ i) ↦ (hPropP (QTreeElimTrue x) (QTreeElimTrue y) $$ i)
         {-# REWRITE QTreeElimComputePath #-}


--We show some custom elimination principles



QTreeElim : ∀ {k} {n : ℕ} {P : QTree n → Set k} (d : (t : Tree n) → P [ t ])
            → hPropPredicate P → (t : QTree n) → P t
QTreeElim d contrP = QTreeElimTrue d (λ tx ty → contrP (trunc _ _) tx ty)

{-
QTreeElimComputePathAux : ∀ {k} {n : ℕ} {P : QTree n → Set k} (d : (t : Tree n) → P [ t ])
            (hPropP : hPropPredicate P) → {t₁ t₂ : QTree n} (i : I)
            → QTreeElim d hPropP (trunc t₁ t₂ $ i) ≡ ((hPropP (trunc t₁ t₂) (QTreeElim d hPropP t₁) (QTreeElim d hPropP t₂)) $$ i)
QTreeElimComputePathAux d hPropP i = refl
-}



QTreeElimProp : ∀ {k} {n : ℕ} {P : QTree n → Set k}
                → ((t : QTree n) → isProp (P t))
                → ((t : Tree n) → P ([ t ]))
                → ((x y : QTree n) → P x → P y → {i : I} → P (trunc x y $ i))
                → (t : QTree n) → P t
QTreeElimProp propP dtree dtrunc = {!!} --QTreeElimTrue dtree (λ tx ty → {!!})

QTreeRec : ∀ {k} {n : ℕ} {X : Set k} (d : Tree n → X) → hProp X → QTree n → X
QTreeRec d hPropX = QTreeElim d (hPropPredicateConstant hPropX)



QTreeRecPath : ∀ {k} {n : ℕ} {X : Set k} {d : Tree n → X} {hX : hProp X} {x y : QTree n} {i : I}
               → QTreeRec d hX (trunc x y $ i) ≡ hX (QTreeRec d hX x) (QTreeRec d hX y) $ i
QTreeRecPath = {!!}
--{-# REWRITE QTreeRecPath #-}

--QTreeRecPath = {!!}



--We define the operadic structure on QTree

idQTree : QTree (s O)
idQTree = [ idTree ]


γQTree : {m n : ℕ} (k : Fin (s m)) → QTree (s m) → QTree n → QTree (m + n)
γQTree k = QTreeRec (λ t → QTreeRec (λ s → [ γTree k t s ]) trunc)
                    (hProp→ trunc)


NfAltOperadQTree : NfAltOperad QTree
NfAltOperadQTree = record
                     { id = idQTree
                     ; γ = γQTree
                     ; UnitLeft = QTreeElimProp (λ _ → UIP)
                                                (λ t → ap [_] (UnitLeft t))
                                                λ x y eq₁ eq₂ {i} → ≡Trans {y = trunc (γQTree fzero idQTree x) (γQTree fzero idQTree y) $ i}
                                                                           QTreeRecPath
                                                                           (ap₂ (λ x₁ y₁ → trunc x₁ y₁ $ i) eq₁ eq₂)
                     ; UnitRight = λ k → QTreeElimProp (λ _ → UIP)
                                                       (λ t → ap [_] (UnitRight k t))
                                                       λ x y eq₁ eq₂ {i} → ≡Trans {y = trunc (γQTree k x idQTree) (γQTree k y idQTree) $ i}
                                                                                  (ap (λ (f : QTree (s O) → _) → f idQTree) QTreeRecPath)
                                                                                  (ap₂ (λ x y → trunc x y $ i) eq₁ eq₂)
                     ; Assoc₁ = {!!}
                     ; Assoc₂ = {!!}
                     }
