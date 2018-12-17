{-# OPTIONS --rewriting #-}

module QuotientLabelledBinaryTree where

open import Data
open import FibrantUniverse
open import LabelledBinaryTree


--We define labbelled trees quotiented, toward ∞-Mon

postulate
  Qtree : Set
  [_] : Ltree → Qtree

  qNormal : {t : Ltree} → [ t ] ≡ [ normalForm t ]
  
  qe₀• : {t : Ltree} (a : arity t) → [ graft t a (l• e₀) ] ≡ [ graft t a • ]

  qe₀cons : {t : Ltree} (a : arity t) {t₁ t₂ : Ltree+} → [ graft t a (lcons e₀ t₁ t₂) ] ≡ [ graft t a (cons t₁ t₂) ]


module _ {k} {P : Qtree → Set k} (d : (t : Ltree) → P [ t ] )

  (_ : {t : Ltree} → transport P qNormal (d t) ≡ (d (normalForm t)))
  
  (_ : {t : Ltree} → (a : arity t)
       → transport P (qe₀• a) (d (graft t a (l• e₀))) ≡ d (graft t a •))
       
  (_ : {t : Ltree} → (a : arity t) → {t₁ t₂ : Ltree+}
       → transport P (qe₀cons a) (d (graft t a (lcons e₀ t₁ t₂))) ≡ d (graft t a (cons t₁ t₂)))
       
  where
  postulate
    elimQtree : (t : Qtree) → P t
    elimQtreeCompute : (t : Ltree) → elimQtree [ t ] ↦ d t
    {-# REWRITE elimQtreeCompute #-}





QtreeRec : ∀ {k} {A : Set k} (d : Ltree → A)
           → ({t : Ltree} → d t ≡ d (normalForm t))
           → ({t : Ltree} → (a : arity t) → d (graft t a (l• e₀)) ≡ d (graft t a •))
           → ({t : Ltree} → (a : arity t) → {t₁ t₂ : Ltree+} → d (graft t a (lcons e₀ t₁ t₂)) ≡ d (graft t a (cons t₁ t₂)))
           → Qtree → A
QtreeRec d eq₁ eq₂ eq₃ = elimQtree d (≡Trans transportConst eq₁)
                                     (λ a → ≡Trans transportConst (eq₂ a))
                                     λ a → ≡Trans transportConst (eq₃ a) 



-- We define function on QTree ignoring label

module _  {k} {A : Set k} (t∅ : A) (t• : A) (tcons : A → A → A)
          (eq₁ : {a : A} → tcons a t• ≡ a)
          (eq₂ : {a : A} → tcons t• a ≡ a)
          (eq₃ : {a b c : A} → tcons a (tcons b c) ≡ tcons (tcons a b) c) where

       QtreeRec-NoLabel : Qtree → A
       QtreeRec-NoLabel = QtreeRec (elimLtree-NoLabel t∅ t• tcons)
                                   (λ {t} → normalFormElimNoLabel t∅ t• tcons eq₁ eq₂ eq₃ {t})
                                   (elimLtreeGraft•-NoLabel t∅ t• tcons)
                                   (elimLtreeGraftCons-NoLabel t∅ t• tcons)








--We define arity of trees, as a natural number

--Arity : Ltree → ℕ
--Arity = elimLtree-NoLabel (s O) O (_+_)

QArity : Qtree → ℕ
QArity = QtreeRec-NoLabel (s O) O (_+_)
                          +O refl (λ {a b c} → ≡Sym (+Assoc {a} {b} {c}))


