module LabelledTreeOld where

open import Data
open import FiniteSet
open import FibrantUniverse



data Tree : Set where
  • : Tree
  ∅ : Tree
  cons : {n : ℕ} → (Fin (s (s n)) → Tree) → Tree


edge+ : Tree → Set
edge+ • = Fin (s O)
edge+ ∅ = Fin O
edge+ (cons f) = Fin (s O) ∨ Σ (Fin _) (λ k → edge+ (f k))


is≠∅ : Tree → Set
is≠∅ • = ⊤
is≠∅ ∅ = ⊥
is≠∅ (cons f) = ⊤

edge : Tree → Set
edge • = Fin O
edge ∅ = Fin O
edge (cons f) = Σ (Fin _) (λ k → is≠∅ (f k) ∨ edge (f k))


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
            → edge (γTree t T) → edge t ∨ Σ (Fin (arity t)) (λ k → is≠∅ (T k) ∨ edge (T k))
-} 


edgeγTree : (t : Tree) → (T : Fin (arity t) → Tree)
            → edge (γTree t T) → edge t ∨ Σ (Fin (arity t)) (λ k → is≠∅ (T k) ∨ edge (T k))
edgeγTree ∅ T e = right (fzero , (right e))
edgeγTree (cons f) T (k , left x) = {!!}
edgeγTree (cons f) T (k , right e) = {!!}







{-

subst : ∀ {k} {A : Set k} {n : ℕ} (f : Fin n → A) (k : Fin n) → A → Fin n → A
subst = {!!}

forget : ∀ {k} {A : Set k} {n : ℕ} (f : Fin (s n) → A) (k : Fin (s n)) → Fin n → A
forget = {!!}

flip : Fin (s (s O)) → Fin (s (s O))
flip x = {!!}

--ContrTreeAux : {n m : ℕ} {k : Fin (s n)} 
--ContrTreeAux 

ContrTree : (t : Tree) → edge t → Tree
--ContrTree • () 
--ContrTree ∅ () 
ContrTree (cons f) (k , left _) with (f k)
ContrTree (cons {O} f) (k , left _) | • = f (flip k)
ContrTree (cons {s n} f) (k , left _) | • = cons (forget f k)
--ContrTree (cons f) (k , left ()) | ∅
ContrTree (cons f) (k , left _) | (cons g) = {!!}
ContrTree (cons f) (k , right e) = cons (subst f k (ContrTree (f k) e))

ContrEdge : {t : Tree} {e : edge t} → edge (ContrTree t e) → edge t
ContrEdge = {!!}

{-
Contrtree : (t : Tree) → edge t → Tree
contrTree • ()
contrTree ∅ ()
contrTree (cons f) (k , e) with (f k)
contrTree (cons f) (k , fzero) | • = {!!} 
contrTree (cons f) (k , ()) | ∅ 
contrTree (cons f) (k , left fzero) | cons g = {!!}
contrTree (cons f) (k , right x) | cons g = {!!}
-}
-}
