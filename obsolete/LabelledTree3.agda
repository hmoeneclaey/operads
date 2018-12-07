module LabelledTree3 where

open import Data
open import FiniteSet
open import FibrantUniverse


data Tree : Set where
  ∅ : Tree
  cons : {n : ℕ} → (Fin n → Tree) → Tree


data Cons : Tree → Set where
  isCons : {n : ℕ} → {f : Fin n → Tree} → Cons (cons f)


decidableCons : (t : Tree) → Cons t ∨ (∅ ≡ t)
decidableCons ∅ = right refl
decidableCons (cons x) = left isCons


data edge : Tree → Set where

  baseEdge : {n : ℕ} {f : Fin n → Tree} (k : Fin n)
             → Cons (f k) → edge (cons f)
             
  highEdge : {n : ℕ} {f : Fin n → Tree} (k : Fin n)
             → edge (f k) → edge (cons f)



data arity : Tree → Set where
  
  arity∅ : arity ∅

  arityCons : {n : ℕ} {f : Fin n → Tree} (k : Fin n) → arity (f k) → arity (cons f)






--We define grafting of tree

γTree : (t : Tree) → (arity t → Tree) → Tree
γTree ∅ T = T arity∅
γTree (cons f) T = cons (λ k → γTree (f k) (T o arityCons k))


Consγ₁ : {t : Tree} → {T : arity t → Tree} → Cons t → Cons (γTree t T)
Consγ₁ isCons = isCons

Consγ₂ : {t : Tree} → {T : arity t → Tree} → (k : arity t) → Cons (T k) → Cons(γTree t T)
Consγ₂ {∅} arity∅ consT = consT
Consγ₂ {cons x} _ _ = isCons




--we show that edge (γ t T) is what we expect. Perhaps we are not using the good method

data edgeγ (t : Tree) (T : arity t → Tree) : Set where
  e1 : edge t → edgeγ t T
  e2 : (a : arity t) → edge (T a) → edgeγ t T
  e3 : Cons t → (a : arity t) → Cons (T a) → edgeγ t T
  

--We define a function

edgeBottom : {t : Tree} {T : arity t → Tree} → edge t → edge (γTree t T)
edgeBottom (baseEdge k consTk) = baseEdge k (Consγ₁ consTk)
edgeBottom (highEdge k e) = highEdge k (edgeBottom e)

edgeTop : {t : Tree} {T : arity t → Tree} → (a : arity t) → edge (T a) → edge (γTree t T)
edgeTop arity∅ e = e
edgeTop (arityCons k a) e = highEdge k (edgeTop a e)

edgeLim : {t : Tree} {T : arity t → Tree} → Cons t → (a : arity t) → Cons (T a) → edge (γTree t T)
edgeLim {t = cons f} isCons (arityCons k a) consTa with decidableCons (f k)
edgeLim {t = cons f} isCons (arityCons k a) consTa | left consfk =  highEdge k (edgeLim consfk a consTa)
edgeLim {t = cons f} isCons (arityCons k a) consTa | right _ = baseEdge k (Consγ₂ a consTa)

edgeγ₁ : {t : Tree} {T : arity t → Tree} → edgeγ t T → edge (γTree t T)
edgeγ₁ (e1 e) = edgeBottom e
edgeγ₁ (e2 a e) = edgeTop a e
edgeγ₁ (e3 const a consTa) = edgeLim const a consTa


--We define its inverse

edgeγConsAux : {t : Tree} {T : arity t → Tree} (p : ∅ ≡ t)
               → Cons (γTree t T) → Cons (T (transport arity p arity∅))
edgeγConsAux refl x = x

edgeγCons : {n : ℕ} {f : Fin n → Tree} {T : arity (cons f) → Tree} (k : Fin n)
                   → Cons (γTree (f k) (λ a → T (arityCons k a))) → edgeγ (cons f) T
edgeγCons {f = f} k consH with decidableCons (f k)
edgeγCons {f = f} k consH | left x = e1 (baseEdge k x)
edgeγCons {f = f} k consH | right p = e3 isCons (arityCons k (transport arity p arity∅)) (edgeγConsAux p consH)

edgeγEdge : {n : ℕ} {f : Fin n → Tree} (T : arity (cons f) → Tree) (k : Fin n)
                   → edgeγ (f k) (λ a → T (arityCons k a)) → edgeγ (cons f) T
edgeγEdge T k (e1 e) = e1 (highEdge k e)
edgeγEdge T k (e2 a e) = e2 (arityCons k a) e
edgeγEdge T k (e3 x a consT) = e3 isCons (arityCons k a) consT

edgeγ₂ : {t : Tree} {T : arity t → Tree} → edge (γTree t T) → edgeγ t T
edgeγ₂ {∅} = e2 arity∅
edgeγ₂ {cons f} (baseEdge k consH) = edgeγCons k consH
edgeγ₂ {cons f} (highEdge k e) = edgeγEdge _ k (edgeγ₂ e) 




--We check they are inverse




--Wrong !!!

invLeftEdgeγAux : {n : ℕ} {f : Fin n → Tree} (T : arity (cons f) → Tree) (k : Fin n) (e : edgeγ (f k) (T o arityCons k))
                  → highEdge k (edgeγ₁ e) ≡ edgeγ₁ (edgeγEdge T k e)

invLeftEdgeγAux T k (e1 _) = refl
invLeftEdgeγAux T k (e2 _ _) = refl
invLeftEdgeγAux {f = f} T k (e3 x a consT) with decidableCons (f k)
invLeftEdgeγAux {f = f} T k (e3 x a consT) | right p = {!!}
invLeftEdgeγAux {f = f} T k (e3 const a consT) | left const' = {!const!}


invLeftEdgeγ : {t : Tree} {T : arity t → Tree} (e : edge (γTree t T)) → e ≡ edgeγ₁ (edgeγ₂ {t = t} e)

invLeftEdgeγ {∅} e = refl

invLeftEdgeγ {cons f} (baseEdge k consH) = {!!}

invLeftEdgeγ {cons f} {T} (highEdge k EE) = ≡Trans (ap (highEdge k) (invLeftEdgeγ {t = f k}EE))
                                                   (invLeftEdgeγAux T k (edgeγ₂ EE))
