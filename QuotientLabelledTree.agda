{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

module QuotientLabelledTree where

open import Data
open import FiniteSet
open import LabelledTree
open import RewritingLabelledTree
open import AltOperad
open import FibrantUniverse



--We define the operad structure on labelled trees

instance
  OpLtree : AltOperad Ltree
  OpLtree = record
              { idAlt = idLtree
              ; γAlt = γLtree
              ; unitAlt₁ = {!!}
              ; unitAlt₂ = {!!}
              ; assocAlt₁ = {!!}
              ; assocAlt₂ = {!!}
              }



--We postulate quotiented trees and show some eliminations principle

postulate
  Qtree : ℕ → Set
  [_] : {n : ℕ} → Ltree n → Qtree n
  Qtree⇒ : {n : ℕ} {t₁ t₂ : Ltree n} → t₁ ⇒ t₂ → [ t₁ ] ≡ [ t₂ ]


mkQtree : {n : ℕ} → Ltree n → Qtree n
mkQtree t = [ t ]

module _ {k} {n : ℕ} {P : Qtree n → Set k}
         (d : (t : Ltree n) → P [ t ])
         (eq : {t₁ t₂ : Ltree n} (r : t₁ ⇒ t₂) → transport P (Qtree⇒ r) (d t₁) ≡ d t₂ ) where

       postulate
         QtreeElim : (t : Qtree n) → P t
         QtreeCompute : (t : Ltree n) → QtreeElim [ t ] ↦ d t
         {-# REWRITE QtreeCompute #-}


module _ {k} {n : ℕ} {X : Set k}
         (d : (t : Ltree n) → X)
         (eq : {t₁ t₂ : Ltree n} (r : t₁ ⇒ t₂) → d t₁ ≡ d t₂) where

       QtreeRec : Qtree n → X
       QtreeRec = QtreeElim d (λ r → ≡Trans transportConst (eq r))


module _ {k} {n : ℕ} {P : Qtree n → Set k}
         (d : (t : Ltree n) → P [ t ])
         (propP : {t : Qtree n} → isProp (P t)) where

       QtreeProp : (t : Qtree n) → P t
       QtreeProp = QtreeElim d (λ _ → propP)




--We show Qtree n contractible

≡transportPath : ∀ {k} {X : Set k} {x y₁ y₂ : X} {p : x ~~> y₁} {q : y₁ ≡ y₂} {i : I}
                 → transport (λ y → x ~~> y) q p $ i ≡ p $ i
≡transportPath {q = refl} = refl

Qtree⇒* : {n : ℕ} {t₁ t₂ : Ltree n} → t₁ ⇒* t₂ → [ t₁ ] ≡ [ t₂ ]
Qtree⇒* rewriteO = refl
Qtree⇒* (rewriteS r x) = ≡Trans (Qtree⇒* r) (Qtree⇒ x)


ContrQtree : {n : ℕ} → Contr (Qtree n)

ContrQtree = record { center = [ μ ] ;
                      path = QtreeElim (λ t → mkPath (λ i → [ i ∩tree t ])
                                                     (Qtree⇒* ⇒*∩tree₀)
                                                     (ap [_] ≡∩tree₁)) 
                                       λ {t₁} r → ≡Path (λ i → ≡Trans (≡transportPath {q = Qtree⇒ r})
                                                                      (Qtree⇒ (∩tree⇒ r)) )}



--Auxiliary results

transport[] : {m n : ℕ} {t : Ltree m} {p : m ≡ n} → transport Qtree p [ t ] ≡ [ transport Ltree p t ]
transport[] {p = refl} = refl



--We construct the operad of quotiented trees, using the operad structure on labelled trees

γQtree : {m n : ℕ} → Qtree m → Fin m → Qtree n → Qtree (pred (m + n))

γQtree = QtreeRec (λ t₁ k → QtreeRec (λ t₂ → [ γLtree t₁ k t₂ ])
                  λ r → Qtree⇒ (γLtreeRight⇒ r))
                  λ r → funext (λ _ → funext (QtreeProp (λ t₃ → Qtree⇒ (γLtreeLeft⇒ r)) UIP) )

idQtree : Qtree (s O)
idQtree = [ idLtree ]


instance
  OpQtree : AltOperad Qtree
  OpQtree = record
              { idAlt = idQtree
              
              ; γAlt = γQtree
              
              ; unitAlt₁ = QtreeProp (λ t → ap [_] (unitAlt₁ t)) UIP
              
              ; unitAlt₂ = QtreeProp (λ t → ap [_] (unitAlt₂ t)) (PropImp→ UIP)
              
              ; assocAlt₁ = QtreeProp (λ t₁ → QtreeProp (λ t₂ → QtreeProp (λ t₃
                                      → ≡Trans (ap [_] (assocAlt₁ t₁ t₂ t₃)) (≡Sym transport[]))
                                               (PropImp→ (PropImp→ UIP)))
                                        (Prop→ (PropImp→ (PropImp→ UIP))))
                                 (Prop→ (Prop→ (PropImp→ (PropImp→ UIP))))
                               
              ; assocAlt₂ = QtreeProp (λ t₁ → QtreeProp (λ t₂ → QtreeProp (λ t₃ eq
                                      → ≡Trans (ap [_] (assocAlt₂ t₁ t₂ t₃ eq)) (≡Sym transport[]))
                                               (PropImp→ (PropImp→ (Prop→ UIP))))
                                        (Prop→ (PropImp→ (PropImp→ (Prop→ UIP)))))
                                 (Prop→ (Prop→ (PropImp→ (PropImp→ (Prop→ UIP)))))
              }


QtreeRecOperad : ∀ {k} {P : ℕ → Set k} {{_ : AltOperad P}}
                 {α : {n : ℕ} → Ltree n → P n} (homα : HomAltOperad {{OpLtree}} α)
                 {α⇒ : {n : ℕ} {t₁ t₂ : Ltree n} → t₁ ⇒ t₂ → α t₁ ≡ α t₂}
                 → HomAltOperad {{OpQtree}} (QtreeRec α α⇒)
QtreeRecOperad record { HomIdAlt = αId ;
                        HomγAlt = αγ }
             = record { HomIdAlt = αId ;
                        HomγAlt = QtreeProp (λ t₁ → QtreeProp (λ t₂ → αγ t₁ t₂)
                                            UIP) (PropImp→ (Prop→ UIP)) }

