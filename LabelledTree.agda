{-# OPTIONS --rewriting #-}

module LabelledTree where

open import Data
open import FiniteSet
open import FibrantUniverse



--We define trees with labelled on the root, and tree without

data Ltree+ : Set where
  ∅+ : Ltree+
  cons+ : {n : ℕ} → I → (Fin n → Ltree+) → Ltree+

data Ltree : Set where
  ∅ : Ltree
  cons : {n : ℕ} → (Fin n → Ltree+) → Ltree


data arity+ : Ltree+ → Set where
  ar∅+ : arity+ ∅+
  arCons+ : {n : ℕ} (f : Fin n → Ltree+) (k : Fin n) (i : I)
            → arity+ (f k) → arity+ (cons+ i f)

data arity : Ltree → Set where
  ar∅ : arity ∅
  arCons : {n : ℕ} (f : Fin n → Ltree+) (k : Fin n)
            → arity+ (f k) → arity (cons f)





--Some preliminary about functions out of a canonical finite set


subst : ∀ {k} {A : Set k} {n : ℕ} (f : Fin n → A) (k : Fin n) → A → Fin n → A
subst f fzero a fzero = a
subst f fzero a (fsucc l) = f (fsucc l)
subst f (fsucc k) a fzero = f fzero
subst f (fsucc k) a (fsucc l) = subst (f o fsucc) k a l

pred : ℕ → ℕ
pred O = O
pred (s n) = n 


FinConcatAux : {m n : ℕ} → (k : Fin (s n)) → Fin (n + m) → Fin (s n) ∨ Fin m 
FinConcatAux fzero = {!!}
FinConcatAux (fsucc k) = {!!}

FinConcat : ∀ {k} {A : Set k} {m n : ℕ} → (f : Fin n → A) → (k : Fin n) → (g : Fin m → A) → Fin (pred n + m) → A 
FinConcat f fzero g l = ∨Elim f g (FinConcatAux fzero l)
FinConcat f (fsucc k) g l = ∨Elim f g (FinConcatAux (fsucc k) l) 





--Basic manipulation of trees

forgetLbl : Ltree+ → Ltree
forgetLbl ∅+ = ∅
forgetLbl (cons+ i f) = cons f

addLbl : I → Ltree → Ltree+
addLbl i ∅ = ∅+
addLbl i (cons f) = cons+ i f




--We define the grafting of two trees

graft++ : (t₁ : Ltree+) (a : arity+ t₁) → Ltree+ → Ltree+
graft++ .∅+ ar∅+ t₂ = t₂
graft++ .(cons+ _ f) (arCons+ f k i a) t₂ = cons+ i (subst f k (graft++ (f k) a t₂))

graft+ : (t₁ : Ltree) (a : arity t₁) (t₂ : Ltree+) → Ltree
graft+ .∅ ar∅ t₂ = forgetLbl t₂
graft+ .(cons f) (arCons f k a) t₂ = cons (subst f k (graft++ (f k) a t₂))

graft : (t₁ : Ltree) (a : arity t₁) → I → Ltree → Ltree
graft t₁ a i t₂ = graft+ t₁ a (addLbl i t₂)




--We define the contraction of tree at a node

ContrTree+ : {n : ℕ} (i : I) (f : Fin n → Ltree+) (a : arity+ (cons+ i f)) (t₂ : Ltree) → Ltree+
ContrTree+ i₁ f (arCons+ .f k _ a) t₂ with (f k)
ContrTree+ i₁ f (arCons+ .f k .i₁ _) ∅ | ∅+ = cons+ i₁ f
ContrTree+ i₁ f (arCons+ .f k .i₁ _) (cons g) | ∅+ = cons+ i₁ (FinConcat f k g) 
ContrTree+ i₁ f (arCons+ .f k _ a) t₂ | cons+ i₂ g = cons+ i₁ (subst f k (ContrTree+ i₂ g a t₂))


ContrTree : (t₁ : Ltree) (a : arity t₁) (t₂ : Ltree) → Ltree
ContrTree .∅ ar∅ t₂ = t₂
ContrTree .(cons f) (arCons f k a) t₂ with (f k)
ContrTree .(cons f) (arCons f k a) ∅ | ∅+ = cons f
ContrTree .(cons f) (arCons f k a) (cons g) | ∅+ = cons (FinConcat f k g)
ContrTree .(cons f) (arCons f k a) t₂ | cons+ i g = cons (subst f k (ContrTree+ i g a t₂))



--Now for the quotient by relevant equalities

postulate
  Qtree : Set
  [_] : Ltree → Qtree
  quotient : (t₁ : Ltree) → (a : arity t₁) → (t₂ : Ltree) → [ graft t₁ a e₀ t₂ ] ≡ [ ContrTree t₁ a t₂ ]
  
module _ {k} {P : Qtree → Set k} (d : (t : Ltree) → P [ t ])
             (_ : (t₁ : Ltree) → (a : arity t₁) → (t₂ : Ltree)
             → transport P (quotient t₁ a t₂) (d (graft t₁ a e₀ t₂)) ≡ d (ContrTree t₁ a t₂)) where
  postulate
    QtreeElim : (x : Qtree) → P x
    QtreeCompute : (t : Ltree) → QtreeElim [ t ] ↦ d t 
    {-# REWRITE QtreeCompute #-}




module tests where

  tree1 : Ltree
  tree1 = cons {n = s (s O)} (λ { fzero → ∅+ ;
                                  (fsucc _) → ∅+})
                                  
  a : arity tree1
  a = arCons _ fzero ar∅+

  tree3 : Ltree
  tree3 = cons {n = (s (s O))} (λ { fzero → addLbl e₀ tree1 ; (fsucc _) → ∅+})

  testingmore : graft tree1 a e₀ tree1 ≡ tree3
  testingmore = ap cons (funext (λ { fzero → refl ; (fsucc k) → refl})) 
