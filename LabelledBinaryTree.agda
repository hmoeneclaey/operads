{-# OPTIONS --rewriting #-}


module LabelledBinaryTree where


open import Data
open import FibrantUniverse


data Ltree+ : Set where
  ∅ : Ltree+
  • : Ltree+
  l• : (i : I) → Ltree+
  cons : Ltree+ → Ltree+ → Ltree+
  lcons : (i : I) → Ltree+ → Ltree+ → Ltree+

data Ltree : Set  where
  ∅ : Ltree
  • : Ltree
  cons : Ltree+ → Ltree+ → Ltree


data arity+ : Ltree+ → Set where
  ar∅+ : arity+ ∅
  arConsL+ : {t₁ t₂ : Ltree+} → arity+ t₁ → arity+ (cons t₁ t₂)
  arConsR+ : {t₁ t₂ : Ltree+} → arity+ t₂ → arity+ (cons t₁ t₂)
  arlConsL+ : {t₁ t₂ : Ltree+} {i : I} → arity+ t₁ → arity+ (lcons i t₁ t₂)
  arlConsR+ : {t₁ t₂ : Ltree+} {i : I} → arity+ t₂ → arity+ (lcons i t₁ t₂)

data arity : Ltree → Set where
  ar∅ : arity ∅
  arConsL : {t₁ t₂ : Ltree+} → arity+ t₁ → arity (cons t₁ t₂)
  arConsR : {t₁ t₂ : Ltree+} → arity+ t₂ → arity (cons t₁ t₂)




--basic operation on trees

forgetLbl : Ltree+ → Ltree
forgetLbl ∅ = ∅
forgetLbl • = •
forgetLbl (l• _) = •
forgetLbl (cons t₁ t₂) = cons t₁ t₂
forgetLbl (lcons _ t₁ t₂) = cons t₁ t₂

addLbl : I → Ltree → Ltree+
addLbl i ∅ = ∅
addLbl i • = l• i
addLbl i (cons t₁ t₂) = lcons i t₁ t₂



-- We define grafting

graft+ : (t₁ : Ltree+) → arity+ t₁ → Ltree+ → Ltree+
graft+ ∅ _ t₂ = t₂
graft+ (cons t₁ t₃) (arConsL+ a) t₂ = cons (graft+ t₁ a t₂) t₃
graft+ (cons t₁ t₃) (arConsR+ a) t₂ = cons t₁ (graft+ t₃ a t₂)
graft+ (lcons i t₁ t₃) (arlConsL+ a) t₂ = lcons i (graft+ t₁ a t₂) t₃
graft+ (lcons i t₁ t₃) (arlConsR+ a) t₂ = lcons i t₁ (graft+ t₃ a t₂)

graft : (t₁ : Ltree) → arity t₁ → Ltree+ → Ltree
graft ∅ _ t₂ = forgetLbl t₂
graft (cons t₁ t₃) (arConsL a) t₂ = cons (graft+ t₁ a t₂) t₃
graft (cons t₁ t₃) (arConsR a) t₂ = cons t₁ (graft+ t₃ a t₂)


--graft : (t₁ : Ltree) → arity t₁ → I → Ltree → Ltree
--graft t₁ a i t₂ = graft+ t₁ a (addLbl i t₂)





--We list all the cases, so that we do not forget anything
--This should be changed at some point...

-- A tree is in normal form if :
-- No • appear in it (except •, which is a normal form)
-- If cons t₁ t₂ appear in it, t₂ is (l• i) or (lcons i t t')
-- If lcons i t₁ t₂ appear in it, t₂ is (l• j) or (lcons j t t')



--Output the normal form of cons t₁ t₂ for t₁ t₂ in normal form
normalFormCons+ : Ltree+ → Ltree+ → Ltree+
normalFormCons+ t₁ • = t₁
normalFormCons+ • t₂ = t₂
normalFormCons+ t₁ (cons t₂ t₃) = cons (normalFormCons+ t₁ t₂) t₃
normalFormCons+ t₁ t₂ = cons t₁ t₂


{- We write the full form for "clarity"...

normalFormCons+ : Ltree+ → Ltree+ → Ltree+
normalFormCons+ ∅ ∅ = cons ∅ ∅
normalFormCons+ ∅ • = ∅
normalFormCons+ ∅ (l• i) = cons ∅ (l• i)
normalFormCons+ ∅ (cons t₂ t₃) = cons (normalFormCons+ ∅ t₂) t₃
normalFormCons+ ∅ (lcons i t₂ t₃) = cons ∅ (lcons i t₂ t₃)
normalFormCons+ • ∅ = ∅
normalFormCons+ • • = •
normalFormCons+ • (l• i) = l• i
normalFormCons+ • (cons t₂ t₃) = cons t₂ t₃
normalFormCons+ • (lcons i t₂ t₃) = lcons i t₂ t₃
normalFormCons+ (l• i) ∅ = cons (l• i) ∅
normalFormCons+ (l• i) • = l• i
normalFormCons+ (l• i) (l• j) = cons (l• i) (l• j)
normalFormCons+ (l• i) (cons t₂ t₃) = cons (normalFormCons+ (l• i) t₂) t₃
normalFormCons+ (l• i) (lcons j t₂ t₃) = cons (l• i) (lcons j t₂ t₃)
normalFormCons+ (cons t₁ t₃) ∅ = cons (cons t₁ t₃) ∅
normalFormCons+ (cons t₁ t₃) • = cons t₁ t₃
normalFormCons+ (cons t₁ t₃) (l• i) = cons (cons t₁ t₃) (l• i)
normalFormCons+ (cons t₁ t₃) (cons t₂ t₄) = cons (normalFormCons+ (cons t₁ t₃) t₂) t₄
normalFormCons+ (cons t₁ t₃) (lcons i t₂ t₄) = cons (cons t₁ t₃) (lcons i t₂ t₄)
normalFormCons+ (lcons i t₁ t₃) ∅ = cons (lcons i t₁ t₃) ∅
normalFormCons+ (lcons i t₁ t₃) • = lcons i t₁ t₃
normalFormCons+ (lcons i t₁ t₃) (l• j) = cons (lcons i t₁ t₃) (l• j)
normalFormCons+ (lcons i t₁ t₃) (cons t₂ t₄) = cons (normalFormCons+ (lcons i t₁ t₃) t₂) t₄
normalFormCons+ (lcons i t₁ t₃) (lcons j t₂ t₄) = cons (lcons i t₁ t₃) (lcons j t₂ t₄)
-}


--Output the normal form of lcons  i t₁ t₂ for t₁ and t₂ in normal form
normalFormLcons+ : I → Ltree+ → Ltree+ → Ltree+
normalFormLcons+ i • • = l• i
normalFormLcons+ i (l• j) • = l• (i ∪ j)
normalFormLcons+ i (lcons j t₁ t₂) • = lcons (i ∪ j) t₁ t₂
normalFormLcons+ i (cons t₁ t₂) • = lcons i t₁ t₂
normalFormLcons+ i ∅ • = ∅
normalFormLcons+ i • ∅ = ∅
normalFormLcons+ i • (l• j) = l• (i ∪ j)
normalFormLcons+ i • (lcons j t₂ t₃) = lcons (i ∪ j) t₂ t₃
normalFormLcons+ i t₁ (cons t₂ t₃) = lcons i (normalFormCons+ t₁ t₂) t₃
normalFormLcons+ i t₁ t₂ = lcons i t₁ t₂

{-
normalFormLcons+ : I → Ltree+ → Ltree+ → Ltree+
normalFormLcons+ i ∅ ∅ = lcons i ∅ ∅
normalFormLcons+ i ∅ • = ∅
normalFormLcons+ i ∅ (l• j) = lcons i ∅ (l• j)
normalFormLcons+ i ∅ (cons t₂ t₃) = lcons i (normalFormCons+ ∅ t₂) t₃
normalFormLcons+ i ∅ (lcons j t₂ t₃) = lcons i ∅ (lcons j t₂ t₃)
normalFormLcons+ i • ∅ = ∅
normalFormLcons+ i • • = l• i
normalFormLcons+ i • (l• j) = l• (i ∪ j)
normalFormLcons+ i • (cons t₂ t₃) = lcons i t₂ t₃
normalFormLcons+ i • (lcons j t₂ t₃) = lcons (i ∪ j) t₂ t₃
normalFormLcons+ i (l• j) ∅ = lcons i (l• j) ∅
normalFormLcons+ i (l• j) • = l• (i ∪ j)
normalFormLcons+ i (l• j) (l• k) = lcons i (l• j) (l• k)
normalFormLcons+ i (l• j) (cons t₂ t₃) = lcons i (normalFormCons+ (l• j) t₂) t₃
normalFormLcons+ i (l• j) (lcons k t₂ t₃) = lcons i (l• j) (lcons k t₂ t₃)
normalFormLcons+ i (cons t₁ t₃) ∅ = lcons i (cons t₁ t₃) ∅
normalFormLcons+ i (cons t₁ t₃) • = lcons i t₁ t₃
normalFormLcons+ i (cons t₁ t₃) (l• j) = lcons i (cons t₁ t₃) (l• j)
normalFormLcons+ i (cons t₁ t₃) (cons t₂ t₄) = lcons i (normalFormCons+ (cons t₁ t₃) t₂) t₄
normalFormLcons+ i (cons t₁ t₃) (lcons j t₂ t₄) = lcons i (cons t₁ t₃) (lcons j t₂ t₄)
normalFormLcons+ i (lcons j t₁ t₃) ∅ = lcons i (lcons j t₁ t₃) ∅
normalFormLcons+ i (lcons j t₁ t₃) • = lcons (i ∪ j) t₁ t₃
normalFormLcons+ i (lcons j t₁ t₃) (l• k) = lcons i (lcons j t₁ t₃) (l• k)
normalFormLcons+ i (lcons j t₁ t₃) (cons t₂ t₄) = lcons i (normalFormCons+ (lcons j t₁ t₃) t₂) t₄
normalFormLcons+ i (lcons j t₁ t₃) (lcons k t₂ t₄) = lcons i (lcons j t₁ t₃) (lcons k t₂ t₄)
-}



--Output the normal form of cons t₁ t₂ for t₁ t₂ in normal form

normalFormCons : Ltree+ → Ltree+ → Ltree
normalFormCons t₁ • = forgetLbl t₁
normalFormCons • t₂ = forgetLbl t₂
normalFormCons t₁ (cons t₂ t₃) = cons (normalFormCons+ t₁ t₂) t₃
normalFormCons t₁ t₂ = cons t₁ t₂

{-
normalFormCons : Ltree+ → Ltree+ → Ltree
normalFormCons ∅ ∅ = cons ∅ ∅
normalFormCons ∅ • = ∅
normalFormCons ∅ (l• i) = cons ∅ (l• i)
normalFormCons ∅ (cons t₂ t₃) = cons (normalFormCons+ ∅ t₂) t₃
normalFormCons ∅ (lcons i t₂ t₃) = cons ∅ (lcons i t₂ t₃)
normalFormCons • ∅ = ∅
normalFormCons • • = •
normalFormCons • (l• i) = •
normalFormCons • (cons t₂ t₃) = cons t₂ t₃
normalFormCons • (lcons i t₂ t₃) = cons t₂ t₃
normalFormCons (l• i) ∅ = cons (l• i) ∅
normalFormCons (l• i) • = •
normalFormCons (l• i) (l• j) = cons (l• i) (l• j)
normalFormCons (l• i) (cons t₂ t₃) = cons (normalFormCons+ (l• i) t₂) t₃
normalFormCons (l• i) (lcons j t₂ t₃) = cons (l• i) (lcons j t₂ t₃)
normalFormCons (cons t₁ t₃) ∅ = cons (cons t₁ t₃) ∅
normalFormCons (cons t₁ t₃) • = cons t₁ t₃
normalFormCons (cons t₁ t₃) (l• i) = cons (cons t₁ t₃) (l• i)
normalFormCons (cons t₁ t₃) (cons t₂ t₄) = cons (normalFormCons+ (cons t₁ t₃) t₂) t₄
normalFormCons (cons t₁ t₃) (lcons i t₂ t₄) = cons (cons t₁ t₃) (lcons i t₂ t₄)
normalFormCons (lcons i t₁ t₃) ∅ = cons (lcons i t₁ t₃) ∅
normalFormCons (lcons i t₁ t₃) • = cons t₁ t₃
normalFormCons (lcons i t₁ t₃) (l• j) = cons (lcons i t₁ t₃) (l• j)
normalFormCons (lcons i t₁ t₃) (cons t₂ t₄) = cons (normalFormCons+ (lcons i t₁ t₃) t₂) t₄
normalFormCons (lcons i t₁ t₃) (lcons j t₂ t₄) = cons (lcons i t₁ t₃) (lcons j t₂ t₄)
-}


--Output the normal form of a labbeled tree
normalForm+ : Ltree+ → Ltree+
normalForm+ ∅ = ∅
normalForm+ • = •
normalForm+ (l• i) = l• i
normalForm+ (cons t₁ t₂) = normalFormCons+ (normalForm+ t₁) (normalForm+ t₂)
normalForm+ (lcons i t₁ t₂) = normalFormLcons+ i (normalForm+ t₁) (normalForm+ t₂)

--Output the normal form of a tree
normalForm : Ltree → Ltree
normalForm ∅ = ∅
normalForm • = •
normalForm (cons t₁ t₂) = normalFormCons (normalForm+ t₁) (normalForm+ t₂)



{-
module test where
  test1 = normalForm (cons • ∅)

  l1 : test1 ≡ ∅
  l1 = refl

  test2 = normalForm (cons • (cons ∅ ∅))

  l2 : test2 ≡ cons ∅ ∅
  l2 = refl

  test3 = normalForm (cons (cons ∅ (cons • •)) (cons (cons ∅ •) (cons (cons • •) (cons • ∅))))

  l3 : test3 ≡ cons (cons ∅ ∅) ∅
  l3 = refl

  postulate i j k : I

  test4 = normalForm (cons • (lcons j ∅ ∅))

  l4 : test4 ≡ cons ∅ ∅
  l4 = refl

  test5 = normalForm (cons • (cons • (cons • ∅)))

  l5 : test5 ≡ ∅
  l5 = refl

  test6 = normalForm (cons (cons • •) (lcons i ∅ •))

  l6 : test6 ≡ ∅
  l6 = refl

  test7 = normalForm (cons • (lcons k (lcons i ∅ ∅) (l• j)))

  l7 : test7 ≡ cons (lcons i ∅ ∅) (l• j)
  l7 = refl

  test8 = normalForm (cons ∅ (lcons i • (l• j)))

  l8 : test8 ≡ cons ∅ (l• (i ∪ j))
  l8 = refl
-}


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
    QtreeElim : (t : Qtree) → P t
    QtreeCompute : (t : Ltree) → QtreeElim [ t ] ↦ d t
    {-# REWRITE QtreeCompute #-}




QtreeRec : ∀ {k} {A : Set k} (d : Ltree → A)
           → ({t : Ltree} → d t ≡ d (normalForm t))
           → ({t : Ltree} → (a : arity t) → d (graft t a (l• e₀)) ≡ d (graft t a •))
           → ({t : Ltree} → (a : arity t) → {t₁ t₂ : Ltree+} → d (graft t a (lcons e₀ t₁ t₂)) ≡ d (graft t a (cons t₁ t₂)))
           → Qtree → A
QtreeRec d eq₁ eq₂ eq₃ = QtreeElim d (≡Trans transportConst eq₁)
                                     (λ a → ≡Trans transportConst (eq₂ a))
                                     λ a → ≡Trans transportConst (eq₃ a) 









--We define arity of trees, as a natural number

Arity+ : Ltree+ → ℕ
Arity+ ∅ = s O
Arity+ • = O
Arity+ (l• i) = O
Arity+ (cons t₁ t₂) = Arity+ t₁ + Arity+ t₂
Arity+ (lcons i t₁ t₂) = Arity+ t₁ + Arity+ t₂

Arity : Ltree → ℕ
Arity ∅ = s O
Arity • = O
Arity (cons t₁ t₂) = Arity+ t₁ + Arity+ t₂


{-ArityNormalFormCons+ : {t₁ t₂ : Ltree+} → Arity+ t₁ + Arity+ t₂ ≡ Arity+ (normalFormCons+ t₁ t₂)
ArityNormalFormCons+ {t₁} {•} = {!!}
ArityNormalFormCons+ {•} {t₂} = {!!}
ArityNormalFormCons+ {t₁} {cons t₂ t₃} = {!!}
ArityNormalFormCons+ {t₁} {t₂} = {!!}-}


ArityNormalFormCons+ : {t₁ t₂ : Ltree+} → Arity+ t₁ + Arity+ t₂ ≡ Arity+ (normalFormCons+ t₁ t₂)
ArityNormalFormCons+ {∅} {∅} = refl
ArityNormalFormCons+ {∅} {•} = refl
ArityNormalFormCons+ {∅} {l• i} = refl
ArityNormalFormCons+ {∅} {cons t₂ t₃} = ap₂ (_+_) (ArityNormalFormCons+ {t₁ = ∅} {t₂ = t₂}) refl
ArityNormalFormCons+ {∅} {lcons i t₂ t₃} = refl
ArityNormalFormCons+ {•} {∅} = refl
ArityNormalFormCons+ {•} {•} = refl
ArityNormalFormCons+ {•} {l• i} = refl
ArityNormalFormCons+ {•} {cons t₂ t₃} = refl
ArityNormalFormCons+ {•} {lcons i t₂ t₃} = refl
ArityNormalFormCons+ {l• i} {∅} = refl
ArityNormalFormCons+ {l• i} {•} = refl
ArityNormalFormCons+ {l• i} {l• i₁} = refl
ArityNormalFormCons+ {l• i} {cons t₂ t₃} = ap₂ (_+_) (ArityNormalFormCons+ {t₁ = l• i} {t₂ = t₂}) refl
ArityNormalFormCons+ {l• i} {lcons i₁ t₂ t₃} = refl
ArityNormalFormCons+ {cons t₁ t₃} {∅} = refl
ArityNormalFormCons+ {cons t₁ t₃} {•} = +O
ArityNormalFormCons+ {cons t₁ t₃} {l• i} = refl
ArityNormalFormCons+ {cons t₁ t₃} {cons t₂ t₄} = ≡Trans (≡Sym (+Assoc {l = Arity+ t₁ + Arity+ t₃}))
                                                        (ap₂ (_+_) (ArityNormalFormCons+ {t₁ = cons t₁ t₃} {t₂ = t₂})
                                                                   (refl {a = Arity+ t₄}))
ArityNormalFormCons+ {cons t₁ t₃} {lcons i t₂ t₄} = refl
ArityNormalFormCons+ {lcons i t₁ t₃} {∅} = refl
ArityNormalFormCons+ {lcons i t₁ t₃} {•} = +O
ArityNormalFormCons+ {lcons i t₁ t₃} {l• i₁} = refl
ArityNormalFormCons+ {lcons i t₁ t₃} {cons t₂ t₄} = ≡Trans (≡Sym (+Assoc {l = Arity+ t₁ + Arity+ t₃}))
                                                           (ap₂ (_+_) (ArityNormalFormCons+ {t₁ = lcons i t₁ t₃} {t₂ = t₂})
                                                                      (refl {a = Arity+ t₄}))
ArityNormalFormCons+ {lcons i t₁ t₃} {lcons i₁ t₂ t₄} = refl


{-
ArityNormalFormCons : {t₁ t₂ : Ltree+} → Arity+ t₁ + Arity+ t₂ ≡ Arity (normalFormCons t₁ t₂)
ArityNormalFormCons {∅} {∅} = refl
ArityNormalFormCons {∅} {•} = refl
ArityNormalFormCons {∅} {l• i} = refl
ArityNormalFormCons {∅} {cons t₂ t₃} = ap₂ (_+_) (ArityNormalFormCons+ {t₁ = ∅} {t₂ = t₂}) refl
ArityNormalFormCons {∅} {lcons i t₂ t₃} = refl
ArityNormalFormCons {•} {∅} = refl
ArityNormalFormCons {•} {•} = refl
ArityNormalFormCons {•} {l• i} = refl
ArityNormalFormCons {•} {cons t₂ t₃} = refl
ArityNormalFormCons {•} {lcons i t₂ t₃} = refl
ArityNormalFormCons {l• i} {∅} = refl
ArityNormalFormCons {l• i} {•} = refl
ArityNormalFormCons {l• i} {l• i₁} = refl
ArityNormalFormCons {l• i} {cons t₂ t₃} = ap₂ (_+_) (ArityNormalFormCons+ {t₁ = l• i} {t₂ = t₂}) refl
ArityNormalFormCons {l• i} {lcons i₁ t₂ t₃} = refl
ArityNormalFormCons {cons t₁ t₃} {∅} = refl
ArityNormalFormCons {cons t₁ t₃} {•} = +O
ArityNormalFormCons {cons t₁ t₃} {l• i} = refl
ArityNormalFormCons {cons t₁ t₃} {cons t₂ t₄} = ≡Trans (≡Sym (+Assoc {l = Arity+ t₁ + Arity+ t₃}))
                                                       (ap₂ (_+_) (ArityNormalFormCons+ {t₁ = cons t₁ t₃} {t₂ = t₂})
                                                                  (refl {a = Arity+ t₄}))
ArityNormalFormCons {cons t₁ t₃} {lcons i t₂ t₄} = refl
ArityNormalFormCons {lcons i t₁ t₃} {∅} = refl
ArityNormalFormCons {lcons i t₁ t₃} {•} = +O
ArityNormalFormCons {lcons i t₁ t₃} {l• i₁} = refl
ArityNormalFormCons {lcons i t₁ t₃} {cons t₂ t₄} =  ≡Trans (≡Sym (+Assoc {l = Arity+ t₁ + Arity+ t₃}))
                                                           (ap₂ (_+_) (ArityNormalFormCons+ {t₁ = lcons i t₁ t₃} {t₂ = t₂})
                                                                      (refl {a = Arity+ t₄}))
ArityNormalFormCons {lcons i t₁ t₃} {lcons i₁ t₂ t₄} = refl


ArityNormalForm+ : {t : Ltree+} → Arity+ t ≡ Arity+ (normalForm+ t)
ArityNormalForm+ {∅} = refl
ArityNormalForm+ {•} = refl
ArityNormalForm+ {l• i} = refl
ArityNormalForm+ {cons t₁ t₂} =  ≡Trans {y = Arity+ (normalForm+ t₁) + Arity+ (normalForm+ t₂)}
                                        (ap₂ (_+_) (ArityNormalForm+ {t = t₁}) (ArityNormalForm+ {t = t₂}))
                                        (ArityNormalFormCons+ {t₁ = normalForm+ t₁} {t₂ = normalForm+ t₂})
ArityNormalForm+ {lcons i t t₁} = {!!}


ArityNormalForm : {t : Ltree} → Arity t ≡ Arity (normalForm t)
ArityNormalForm {∅} = refl
ArityNormalForm {•} = refl
ArityNormalForm {cons t₁ t₂} = ≡Trans {y = Arity+ (normalForm+ t₁) + Arity+ (normalForm+ t₂)}
                                      (ap₂ (_+_) (ArityNormalForm+ {t = t₁}) (ArityNormalForm+ {t = t₂}))
                                      (ArityNormalFormCons {t₁ = normalForm+ t₁} {t₂ = normalForm+ t₂})


QArity : Qtree → ℕ
QArity = QtreeRec Arity
                  (λ {t} → ArityNormalForm {t})
                  {!!}
                  {!!}
-}
