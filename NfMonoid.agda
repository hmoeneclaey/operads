{-# OPTIONS --rewriting #-}

module NfMonoid where


open import Data
open import FiniteSet
open import NfOperad
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

γTree : {n : ℕ} {S : Fin n → ℕ} → Tree n → ((k : Fin n) → Tree (S k)) → Tree (finiteSum S)
γTree • _ = •
γTree {S = S} ∅ d = transport Tree (Nfη₁ S) (d fzero)
γTree (cons t₁ t₂) d = {!cons (γTree t₁ (d o Fin+Left)) (γTree t₂ (d o Fin+Right))!}

instance
  NfOperadTree : NfOperad Tree
  NfOperadTree = record
                   { NfId = idTree
                   ; Nfγ = γTree
                   ; NfUnitLeft = {!!}
                   ; NfUnitRight = {!!}
                   ; NfAssoc = {!!}
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
QTreeElimProp propP dtree dtrunc = QTreeElimTrue dtree (λ tx ty → {!!})

QTreeRec : ∀ {k} {n : ℕ} {X : Set k} (d : Tree n → X) → hProp X → QTree n → X
QTreeRec d hPropX = QTreeElim d (hPropPredicateConstant hPropX)

QTreeRecPath : ∀ {k} {n : ℕ} {X : Set k} {d : Tree n → X} {hX : hProp X} {x y : QTree n} {i : I}
               → QTreeRec d hX (trunc x y $ i) ≡ hX (QTreeRec d hX x) (QTreeRec d hX y) $ i
QTreeRecPath = {!!}



--We define the operadic structure on QTree

idQTree : QTree (s O)
idQTree = [ idTree ]

γQTree : {n : ℕ} {S : Fin n → ℕ} → QTree n
         → ((k : Fin n) → QTree (S k)) → QTree (finiteSum S)
γQTree = QTreeRec (λ t → {!!})
                  (hProp→ trunc)

γQTreeCompute : {n : ℕ} (t : Tree n) {S : Fin n → ℕ} (T : (k : Fin n) → Tree (S k))
                → γQTree [ t ] (λ k → [ T k ]) ≡ [ γTree t T ]
γQTreeCompute = {!!}

γQTreeComputePath : {n : ℕ} {x y : QTree n} {S : Fin n → ℕ} {d : (k : Fin n) → QTree (S k)} {i : I}
                    → γQTree (trunc x y $ i) d ≡ trunc (γQTree x d) (γQTree y d) $ i
γQTreeComputePath {n} {S = S} {d = d} = ap (λ (f : ((k : Fin n) → QTree (S k)) → _) → f d) QTreeRecPath



TransportQTree : {m n : ℕ} {p : m ≡ n} {t : Tree m} → [ transport Tree p t ] ≡ transport QTree p [ t ]
TransportQTree {p = refl} = refl

TransportTrunc : {m n : ℕ} {p : m ≡ n} {x y : QTree m} {i : I}
                 → trunc (transport QTree p x) (transport QTree p y) $ i ≡ transport QTree p (trunc x y $ i)
TransportTrunc {p = refl} = refl

instance
  QTreeMon : NfOperad QTree
  QTreeMon = record
               { NfId = idQTree
               ; Nfγ = γQTree
               ; NfUnitLeft = QTreeElimProp (λ _ → UIP)
                                            (λ t → ≡Trans (γQTreeCompute t (λ _ → idTree))
                                                          (≡Trans (ap [_] (NfUnitLeft t)) TransportQTree))
                                            (λ x y eqx eqy {i} → ≡Trans γQTreeComputePath
                                                                        (≡Trans {y = trunc (transport QTree Nfη₂ x) (transport QTree Nfη₂ y) $ i}
                                                                                (ap₂ (λ x₁ y₁ → trunc x₁ y₁ $ i) eqx eqy)
                                                                                TransportTrunc))
               ; NfUnitRight = {!!}
               ; NfAssoc = {!!}
               }

