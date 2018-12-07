module LabelledTree2 where

open import Data
open import FiniteSet
open import FibrantUniverse

{-
data Tree : Set where
  ∅ : Tree
  cons : {n : ℕ} → (Fin n → Tree) → Tree


is≠∅ : Tree → Set
is≠∅ ∅ = ⊥
is≠∅ (cons f) = ⊤
-}

--data edge : Tree → Set where
--  is≠∅ (f k) → edge (cons f)

--edge : Tree → Set
--edge ∅ = Fin O
--edge (cons {n} f) = Σ (Fin _)


data Tree : Set where
  • : Tree
  ∅ : Tree
  cons : {n : ℕ} → (Fin (s (s n)) → Tree) → Tree

data is≠∅ : Tree → Set where
  isnotid : {n : ℕ} → {f : Fin (s (s n)) → Tree} → is≠∅ (cons f)

data edge : Tree → Set where
  baseEdge : {n : ℕ} {f : Fin (s(s n)) → Tree} (k : Fin (s (s n))) → is≠∅ (f k) → edge (cons f)
  higherEdge : {n : ℕ} {f : Fin (s(s n)) → Tree} (k : Fin (s (s n))) → edge (f k) → edge (cons f)




--Perhaps arity should be a finite set ?

arity : Tree → ℕ
arity • = O
arity ∅ = s O
arity (cons f) = finiteSum (arity o f) 



--This should perhaps go to FiniteSet.agda

finiteSumInc : {n : ℕ} (S : Fin n → ℕ) {k : Fin n} → Fin (S k) → Fin (finiteSum S)
finiteSumInc S {fzero} = Fin+Left
finiteSumInc S {fsucc k} = Fin+Right o finiteSumInc (S o fsucc)



γTree : (t : Tree) → (Fin (arity t) → Tree) → Tree
γTree • _ = •
γTree ∅ f = f fzero
γTree (cons f) F = cons (λ k → γTree (f k) λ m → F (finiteSumInc (arity o f) m))


{-
edgeγTree : (t : Tree) → (T : Fin (arity t) → Tree)
            → edge (γTree t T) → edge t ∨ Σ (Fin (arity t)) (λ k → is≠∅ (T k) ∨ edge (T k))
edgeγTree = {!!}
-}

data edgeγ (t : Tree) (T : Fin (arity t) → Tree) : Set where
  e1 : edge t → edgeγ t T
  e2 : (k : Fin (arity t)) → edge (T k) → edgeγ t T
  e3 : (k : Fin (arity t)) → is≠∅ (T k) → edgeγ t T


{-
edgeγTreeInv : {t : Tree} → {T : Fin (arity t) → Tree}
               → edge t ∨ Σ (Fin (arity t)) (λ k → is≠∅ (T k) ∨ edge (T k)) → edge (γTree t T)
edgeγTreeInv (left (baseEdge k x)) = baseEdge k {!!}
edgeγTreeInv (left (higherEdge k e)) = higherEdge k (edgeγTreeInv (left e)) 
edgeγTreeInv (right (k , left x)) = {!!}
edgeγTreeInv (right (k , right x)) = {!!}
-}
