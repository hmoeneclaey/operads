{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

module QuotientLabelledTree where

open import Data
open import FibrantUniverse
open import LabelledTree
open import FiniteSet
open import MorphismFiniteSet


--We define labbelled trees quotiented, toward ∞-Mon

postulate
  Qtree : Set
  [_] : Ltree → Qtree

  ≡NormalForm : {t : Ltree} → [ t ] ≡ [ normalForm t ]
  
  ≡Graft• : {t : Ltree} (a : arity t) → [ graft t a (l• e₀) ] ≡ [ graft t a • ]

  ≡GraftCons : {t : Ltree} (a : arity t) {t₁ t₂ : Ltree+} → [ graft t a (lcons e₀ t₁ t₂) ] ≡ [ graft t a (cons t₁ t₂) ]


module _ {k} {P : Qtree → Set k} (d : (t : Ltree) → P [ t ] )

  (_ : {t : Ltree} → transport P ≡NormalForm (d t) ≡ (d (normalForm t)))
  
  (_ : {t : Ltree} → (a : arity t)
       → transport P (≡Graft• a) (d (graft t a (l• e₀))) ≡ d (graft t a •))
       
  (_ : {t : Ltree} → (a : arity t) → {t₁ t₂ : Ltree+}
       → transport P (≡GraftCons a) (d (graft t a (lcons e₀ t₁ t₂))) ≡ d (graft t a (cons t₁ t₂)))
       
  where
  postulate
    elimQtree : (t : Qtree) → P t
    elimQtreeCompute : (t : Ltree) → elimQtree [ t ] ↦ d t
    {-# REWRITE elimQtreeCompute #-}




--Now we give some alternative elimination principle for Qtree


QtreeRec : ∀ {k} {A : Set k} (d : Ltree → A)
           → ({t : Ltree} → d t ≡ d (normalForm t))
           → ({t : Ltree} → (a : arity t) → d (graft t a (l• e₀)) ≡ d (graft t a •))
           → ({t : Ltree} → (a : arity t) → {t₁ t₂ : Ltree+} → d (graft t a (lcons e₀ t₁ t₂)) ≡ d (graft t a (cons t₁ t₂)))
           → Qtree → A
           
QtreeRec d eq₁ eq₂ eq₃ = elimQtree d (≡Trans transportConst eq₁)
                                     (λ a → ≡Trans transportConst (eq₂ a))
                                     (λ a → ≡Trans transportConst (eq₃ a)) 


{-


subst : ∀ {k} {A : Set k} {n : ℕ}
        → (f : Fin n → A) (a : Fin n) → A → Fin n → A
subst = {!!}

subst≡Tree1 : {n : ℕ} (t : Fin n → Ltree) (k : Fin n) {t₁ : Ltree}
             →  [ t k ] ≡ [ t₁ ] → (λ k → [ t k ]) ≡ λ k₁ → [ subst t k t₁ k₁ ] 
subst≡Tree1 = {!!}

subst≡Tree2 : {n : ℕ} (t : Fin n → Ltree) (k : Fin n) {t₁ t₂ : Ltree}
             →  [ t₁ ] ≡ [ t₂ ] → (λ k₁ → [ subst t k t₁ k₁ ]) ≡ λ k₁ → [ subst t k t₂ k₁ ] 
subst≡Tree2 = {!!}


module _ {l} {n : ℕ} {P : (Fin n → Qtree) → Set l}

         (d : (t : Fin n → Ltree) → P (λ k → [ t k ]))
         
         (_ : (t : Fin n → Ltree) (k : Fin n) → transport P (subst≡Tree1 t k ≡NormalForm) (d t) ≡ d (subst t k (normalForm (t k))))
         
         (_ : (t : Fin n → Ltree) (k : Fin n) (a : arity (t k))
              → transport P (subst≡Tree2 t k (≡Graft• a))
                (d (subst t k (graft (t k) a (l• e₀)))) ≡ d (subst t k (graft (t k) a •)))

         (_ : (t : Fin n → Ltree) (k : Fin n) (a : arity (t k)) {t₁ t₂ : Ltree+}
              → transport P (subst≡Tree2 t k (≡GraftCons a {t₁} {t₂}))
                (d (subst t k (graft (t k) a (lcons e₀ t₁ t₂)))) ≡ d (subst t k (graft (t k) a (cons t₁ t₂)))) where

  elimQtree-Finite : (t : Fin n → Qtree) → P t
  elimQtree-Finite = {!!}



QtreeRec-Finite : ∀ {l} {n : ℕ} {A : Set l}

                  (d : (Fin n → Ltree) → A)

                  (_ : (t : Fin n → Ltree) (k : Fin n) → d t ≡ d (subst t k (normalForm (t k))))
         
                  (_ : (t : Fin n → Ltree) (k : Fin n) (a : arity (t k))
                       → d (subst t k (graft (t k) a (l• e₀))) ≡ d (subst t k (graft (t k) a •)))

                  (_ : (t : Fin n → Ltree) (k : Fin n) (a : arity (t k)) {t₁ t₂ : Ltree+}
                       → d (subst t k (graft (t k) a (lcons e₀ t₁ t₂))) ≡ d (subst t k (graft (t k) a (cons t₁ t₂))))

                  → (Fin n → Qtree) → A

QtreeRec-Finite {A = A} d eq₁ eq₂ eq₃ = elimQtree-Finite {P = λ _ → A} d
                                                         (λ t k → ≡Trans (transportConst
                                                                         {p = subst≡Tree1 t k ≡NormalForm})
                                                                         (eq₁ t k))
                                                         (λ t k a → ≡Trans (transportConst
                                                                           {p = subst≡Tree2 t k (≡Graft• a)})
                                                                           (eq₂ t k a))
                                                         λ t k a {t₁} {t₂} → ≡Trans (transportConst
                                                                                    {p = subst≡Tree2 t k (≡GraftCons a {t₁} {t₂})})
                                                                                    (eq₃ t k a {t₁} {t₂})

-}


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




elimQtree-Prop : ∀ {k} {P : Qtree → Set k}
                 → ((t : Ltree) → P [ t ])
                 → ({t : Qtree} → isProp (P t))
                 → (t : Qtree) → P t
elimQtree-Prop = {!!}

elimQtree-PropFinite : ∀ {k} {A : Set} {{_ : FOSet A}} {P : (A → Qtree) → Set k}
                       → ((t : A → Ltree) → P (λ k → [ t k ]))
                       → ({t : A → Qtree} → isProp (P t))
                       → (t : A → Qtree) → P t
elimQtree-PropFinite = {!!}


--We define arity of trees, as a natural number

--Arity : Ltree → ℕ
--Arity = elimLtree-NoLabel (s O) O (_+_)

Arity : Qtree → ℕ
Arity = QtreeRec-NoLabel (s O) O (_+_)
                          +O refl (λ {a b c} → ≡Sym (+Assoc {a} {b} {c}))



arityToArity : (t : Ltree) → arity t → Fin (Arity [ t ])
arityToArity .∅ ar∅ = fzero
arityToArity .(cons _ _) (arConsL x) = {!!}
arityToArity .(cons _ _) (arConsR x) = {!!}

ArityToarity : (t : Ltree) → Fin (Arity [ t ]) → arity t
ArityToarity = {!!}

--module test where
--  test1 : Arity [ ∅ ] ≡ s O
--  test1 = refl



postulate γQtree : (t : Qtree) → (Fin (Arity t) → Qtree) → Qtree
postulate γQtreeCompute : {t : Ltree} → {s : Fin (Arity [ t ]) → Ltree}
                          → γQtree [ t ] (λ k → [ s k ]) ≡ [ γLtree t (s o arityToArity t) ]

{-γQtree = elimQtree (λ t → QtreeRec-Finite (λ s → [ γLtree t (s o (arityToArity t)) ])
                                          {!!}
                                          {!!}
                                          {!!})
                   {!!} {!!} {!!}-}



γQtreeUnitLeft : (t : Qtree) → γQtree t (λ _ → [ ∅ ]) ≡ t
γQtreeUnitLeft = elimQtree-Prop (λ t → ≡Trans γQtreeCompute (ap [_] γLtreeUnitLeft)) UIP

γQtreeUnitRight : (t : Fin (s O) → Qtree) → γQtree [ ∅ ] t ≡ t fzero
γQtreeUnitRight = elimQtree-PropFinite (λ t → γQtreeCompute) UIP


γQtreeΣ : (t : Qtree) (s : Fin (Arity t) → Qtree) → Fin (Arity (γQtree t s)) → Σ (Fin (Arity t)) (λ k → Fin (Arity (s k)))
γQtreeΣ = {!!}

γQtreeΣCompute : {t : Ltree} {s : Fin (Arity [ t ]) → Ltree}
                 → γQtreeΣ [ t ] (λ k → [ s k ]) ≡ Σfun (arityToArity t) (λ {a} → arityToArity (s (arityToArity t a))) o
                                                     (γLtreeΣ t (s o arityToArity _)) o (ArityToarity _) o
                                                     (transport (Fin o Arity) (γQtreeCompute {t} {s}))
γQtreeΣCompute = {!!}

HomFOγ : {t : Qtree} {s : Fin (Arity t) → Qtree} → HomFO {{Afinite = canonicalFOSet}} (γQtreeΣ t s)
HomFOγ = {!!}

γQtreeAssoc : (t : Qtree) (s : Fin (Arity t) → Qtree) (v : Σ (Fin (Arity t)) (λ k → Fin (Arity (s k))) → Qtree)
              → γQtree (γQtree t s) (v o (γQtreeΣ t s)) ≡ γQtree t (λ k → γQtree (s k) (λ l → v (k , l)))
              
γQtreeAssoc = elimQtree-Prop (λ t →
                elimQtree-PropFinite (λ s →
                  elimQtree-PropFinite (λ v → {!!})
                  UIP)
                (Prop→ UIP))
              (Prop→ (Prop→ UIP))

