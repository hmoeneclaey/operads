{-# OPTIONS --allow-unsolved-metas #-}

module RewritingLabelledTree where

open import Data
open import LabelledTree
open import FiniteSet
open import FibrantUniverse


--We define auxiliary things for reduction

UnaryVertice : {n : ℕ} → Ltree n → Set
UnaryVertice = {!!}

redUnary : {n : ℕ} (t : Ltree n) → UnaryVertice t → Ltree n
redUnary = {!!}


data InternalVertice+ : {n : ℕ} → Ltree+ n → Set where
  intRoot : {k : ℕ} {S : Fin k → ℕ} {i : I}
            (t : (a : Fin k) → Ltree+ (S a)) → InternalVertice+ (cons+ i t)
  intAbove : {k : ℕ} {S : Fin k → ℕ} {i : I}
             (t : (a : Fin k) → Ltree+ (S a)) (a : Fin k) → InternalVertice+ (t a)→ InternalVertice+ (cons+ i t)

data InternalVertice : {n : ℕ} → Ltree n → Set where
  mkInternalVerice : {k : ℕ} {S : Fin k → ℕ} (t : (a : Fin k) → Ltree+ (S a))
                     (a : Fin k) → InternalVertice+ (t a)→ InternalVertice (cons t) 


cardinalInternalVertice+ : {n : ℕ} → Ltree+ n → ℕ
cardinalInternalVertice+ ∅+ = O
cardinalInternalVertice+ (cons+ i x) = s (finiteSum (λ k → cardinalInternalVertice+ (x k)))

cardinalInternalVertice : {n : ℕ} → Ltree n → ℕ
cardinalInternalVertice ∅ = O
cardinalInternalVertice (cons x) = finiteSum (λ k → cardinalInternalVertice+ (x k))


instance
  FOInternalVertice : {n : ℕ} {t : Ltree n} → FOSet (InternalVertice t)
  FOInternalVertice = {!!}


EvalLtree : {n : ℕ} {t : Ltree n} → InternalVertice t → I
EvalLtree = {!!}

redO : {n : ℕ} (t : Ltree n) → (k : InternalVertice t) → Ltree n
redO = {!!}


--We define the top and bottom tree of an internal vertice

cardinal⊥Ltree : {n : ℕ} {t : Ltree n} → InternalVertice t → ℕ
cardinal⊥Ltree = {!!}

cardinal⊤Ltree : {n : ℕ} {t : Ltree n} → InternalVertice t → ℕ
cardinal⊤Ltree = {!!}

≡cardinal⊥⊤Ltree : {n : ℕ} {t : Ltree n} {k : InternalVertice t} → pred (cardinal⊥Ltree k + cardinal⊤Ltree k) ≡ n
≡cardinal⊥⊤Ltree = {!!}

leaf⊥Ltree : {n : ℕ} {t : Ltree n} (k : InternalVertice t) → Fin (cardinal⊥Ltree k)
leaf⊥Ltree = {!!}

⊥Ltree : {n : ℕ} {t : Ltree n} (k : InternalVertice t) → Ltree (cardinal⊥Ltree k)
⊥Ltree = {!!}

⊤Ltree : {n : ℕ} {t : Ltree n} (k : InternalVertice t) → Ltree (cardinal⊤Ltree k)
⊤Ltree = {!!}

⊥⊤γLtree : {n : ℕ} {t : Ltree n} {k : InternalVertice t}
               → EvalLtree k ≡ e₁
               → t ≡ transport Ltree (≡cardinal⊥⊤Ltree {k = k}) (γLtree (⊥Ltree k) (leaf⊥Ltree k) (⊤Ltree k))
⊥⊤γLtree = {!!}


Internalγ : {m n : ℕ} (t₁ : Ltree m) (k : Fin m) (t₂ : Ltree n) → InternalVertice (γLtree t₁ k t₂)
Internalγ = {!!}

Internalγe₁ : {m n : ℕ} {t₁ : Ltree m} {k : Fin m} {t₂ : Ltree n} → EvalLtree (Internalγ t₁ k t₂) ≡ e₁
Internalγe₁ = {!!}

≡Internalγ⊥ : {m n : ℕ} {t₁ : Ltree m} {k : Fin m} {t₂ : Ltree n} → m ≡ cardinal⊥Ltree (Internalγ t₁ k t₂)
≡Internalγ⊥ = {!!}

≡Internalγ⊤ : {m n : ℕ} {t₁ : Ltree m} {k : Fin m} {t₂ : Ltree n} → n ≡ cardinal⊤Ltree (Internalγ t₁ k t₂)
≡Internalγ⊤ = {!!}

≡Internalγ⊥Ltree : {m n : ℕ} {t₁ : Ltree m} {k : Fin m} {t₂ : Ltree n}
                   → ⊥Ltree (Internalγ t₁ k t₂) ≡ transport Ltree (≡Internalγ⊥ {t₁ = t₁} {k} {t₂}) t₁
≡Internalγ⊥Ltree = {!!}

≡Internalγ⊤Ltree : {m n : ℕ} {t₁ : Ltree m} {k : Fin m} {t₂ : Ltree n}
                   → ⊤Ltree (Internalγ t₁ k t₂) ≡ transport Ltree (≡Internalγ⊤ {t₁ = t₁} {k} {t₂}) t₂
≡Internalγ⊤Ltree = {!!}

≡leaf⊤Ltree : {m n : ℕ} {t₁ : Ltree m} {k : Fin m} {t₂ : Ltree n}
              → leaf⊥Ltree (Internalγ t₁ k t₂) ≡ transport Fin (≡Internalγ⊥ {t₁ = t₁} {k} {t₂}) k
≡leaf⊤Ltree = {!!}

--⊥Ltree (Internalγ )

--We define the rewriting on Ltree

data _⇒_ {n : ℕ} : Ltree n → Ltree n → Set where
  unary⇒ : {t : Ltree n} {e : UnaryVertice t} → t ⇒ redUnary t e
  O⇒ : {t : Ltree n} {e : InternalVertice t} → EvalLtree e ≡ e₀ → t ⇒ redO t e

infix 32 _⇒_

data _⇒*_ {n : ℕ} : Ltree n → Ltree n → Set where
  rewriteO : {t : Ltree n} → t ⇒* t
  rewriteS : {t₁ t₂ t₃ : Ltree n} → t₁ ⇒* t₂ → t₂ ⇒ t₃ → t₁ ⇒* t₃

infix 30 _⇒*_


μ∅⇒ : μ ⇒ ∅
μ∅⇒ = {!!}

γLtreeLeft⇒ : {m n : ℕ} {t₁ t₂ : Ltree m} {k : Fin m} {t : Ltree n}
              → t₁ ⇒ t₂ → γLtree t₁ k t ⇒ γLtree t₂ k t
γLtreeLeft⇒ = {!!}

γLtreeRight⇒ : {m n : ℕ} {t₁ t₂ : Ltree n} {k : Fin m} {t : Ltree m}
               → t₁ ⇒ t₂ → γLtree t k t₁ ⇒ γLtree t k t₂
γLtreeRight⇒ = {!!}

∩tree⇒ : {n : ℕ} {t₁ t₂ : Ltree n} {i : I} → t₁ ⇒ t₂ → i ∩tree t₁ ⇒ i ∩tree t₂
∩tree⇒ = {!!}

⇒*∩tree₀ : {n : ℕ} {t : Ltree n} → e₀ ∩tree t ⇒* μ
⇒*∩tree₀ = {!!}


{-
Confluent⇒ : {n : ℕ} {t₁ t₂ t₃ : LTree n} → t₁ ⇒ t₂ → t₁ ⇒ t₃ → LTree n
Confluent⇒ = {!!}
-}
