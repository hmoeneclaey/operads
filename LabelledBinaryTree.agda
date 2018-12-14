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

addLbl+ : I → Ltree+ → Ltree+
addLbl+ i ∅ = ∅
addLbl+ i • = l• i
addLbl+ i (l• j) = l• (i ∪ j)
addLbl+ i (cons t₁ t₂) = lcons i t₁ t₂
addLbl+ i (lcons j t₁ t₂) = lcons (i ∪ j) t₁ t₂



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





-- Here we define normal form of tree

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


--Output the normal form of lcons  i t₁ t₂ for t₁ and t₂ in normal form
normalFormLcons+ : I → Ltree+ → Ltree+ → Ltree+
normalFormLcons+ i t₁ • = addLbl+ i t₁
normalFormLcons+ i • t₂ = addLbl+ i t₂
normalFormLcons+ i t₁ (cons t₂ t₃) = lcons i (normalFormCons+ t₁ t₂) t₃
normalFormLcons+ i t₁ t₂ = lcons i t₁ t₂



--Output the normal form of cons t₁ t₂ for t₁ t₂ in normal form

normalFormCons : Ltree+ → Ltree+ → Ltree
normalFormCons t₁ • = forgetLbl t₁
normalFormCons • t₂ = forgetLbl t₂
normalFormCons t₁ (cons t₂ t₃) = cons (normalFormCons+ t₁ t₂) t₃
normalFormCons t₁ t₂ = cons t₁ t₂


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



--Now we need lemma to help show that f normalForm t ≡ f t

module _ {k} {A : Set k} (t∅ : A) (t• : A) (tl• : I → A) (tcons : A → A → A) (tlcons : I → A → A → A) where

  elimLtree+ : Ltree+ → A
  elimLtree+ ∅ = t∅
  elimLtree+ • = t•
  elimLtree+ (l• i) = tl• i
  elimLtree+ (cons t₁ t₂) = tcons (elimLtree+ t₁) (elimLtree+ t₂)
  elimLtree+ (lcons i t₁ t₂) = tlcons i (elimLtree+ t₁) (elimLtree+ t₂)

  module _ (eq₁ : {a : A} → tcons a t• ≡ a)
           (eq₂ : {a : A} → tcons t• a ≡ a)
           (eq₃ : {a b c : A} → tcons a (tcons b c) ≡ tcons (tcons a b) c) where

         equalNormalFormCons+ : {t₁ t₂ : Ltree+} → elimLtree+ (cons t₁ t₂) ≡ elimLtree+ (normalFormCons+ t₁ t₂)
         equalNormalFormCons+ {∅} {∅} = refl
         equalNormalFormCons+ {∅} {•} = eq₁
         equalNormalFormCons+ {∅} {l• i} = refl
         equalNormalFormCons+ {∅} {cons t₂ t₃} = ≡Trans eq₃ (ap₂ tcons (equalNormalFormCons+ {∅} {t₂}) refl)
         equalNormalFormCons+ {∅} {lcons i t₂ t₃} = refl
         equalNormalFormCons+ {•} {∅} = eq₂
         equalNormalFormCons+ {•} {•} = eq₂
         equalNormalFormCons+ {•} {l• i} = eq₂
         equalNormalFormCons+ {•} {cons t₂ t₃} = eq₂
         equalNormalFormCons+ {•} {lcons i t₂ t₃} = eq₂
         equalNormalFormCons+ {l• i} {∅} = refl
         equalNormalFormCons+ {l• i} {•} = eq₁
         equalNormalFormCons+ {l• i} {l• i₁} = refl
         equalNormalFormCons+ {l• i} {cons t₂ t₃} =  ≡Trans eq₃ (ap₂ tcons (equalNormalFormCons+ {l• i} {t₂}) refl)
         equalNormalFormCons+ {l• i} {lcons i₁ t₂ t₃} = refl
         equalNormalFormCons+ {cons t₁ t₃} {∅} = refl
         equalNormalFormCons+ {cons t₁ t₃} {•} = eq₁
         equalNormalFormCons+ {cons t₁ t₃} {l• i} = refl
         equalNormalFormCons+ {cons t₁ t₃} {cons t₂ t₄} =  ≡Trans eq₃ (ap₂ tcons (equalNormalFormCons+ {cons t₁ t₃} {t₂}) refl)
         equalNormalFormCons+ {cons t₁ t₃} {lcons i t₂ t₄} = refl
         equalNormalFormCons+ {lcons i t₁ t₃} {∅} = refl
         equalNormalFormCons+ {lcons i t₁ t₃} {•} = eq₁
         equalNormalFormCons+ {lcons i t₁ t₃} {l• i₁} = refl
         equalNormalFormCons+ {lcons i t₁ t₃} {cons t₂ t₄} =  ≡Trans eq₃ (ap₂ tcons (equalNormalFormCons+ {lcons i t₁ t₃} {t₂}) refl)
         equalNormalFormCons+ {lcons i t₁ t₃} {lcons i₁ t₂ t₄} = refl

         module _ (eq₁ : {i : I} → tlcons i t• t∅ ≡ t∅)
                  (eq₂ : {i : I} → tlcons i t• t• ≡ tl• i)
                  (eq₃ : {i j : I} → tlcons i t• (tl• j) ≡ tl• (i ∪ j))
                  (eq₄ : {i : I} {a b : A} → tlcons i (tcons a b) t• ≡ tlcons i a b)
                  (eq₅ : {i j : I} {a b : A} → tlcons i t• (tlcons j a b) ≡ tlcons (i ∪ j) a b)
                  (eq₆ : {i : I} → tlcons i t∅ t• ≡ t∅)
                  (eq₇ : {i j : I} → tlcons i (tl• j) t• ≡ tl• (i ∪ j))
                  (eq₈ : {i j : I} {a b : A} → tlcons i (tlcons j a b) t• ≡ tlcons (i ∪ j) a b)
                  (eq₉ : {i : I} {a b c : A} → tlcons i a (tcons b c) ≡ tlcons i (tcons a b) c) where

                equalNormalFormLcons+ : {i : I} {t₁ t₂ : Ltree+} → elimLtree+ (lcons i t₁ t₂) ≡ elimLtree+ (normalFormLcons+ i t₁ t₂)
                equalNormalFormLcons+ {i} {∅} {∅} = refl
                equalNormalFormLcons+ {i} {∅} {•} = eq₆
                equalNormalFormLcons+ {i} {∅} {l• i₁} = refl
                equalNormalFormLcons+ {i} {∅} {cons t₂ t₃} = ≡Trans eq₉ (ap₂ (tlcons i) (equalNormalFormCons+ {t₁ = ∅} {t₂ = t₂}) refl)
                equalNormalFormLcons+ {i} {∅} {lcons i₁ t₂ t₃} = refl
                equalNormalFormLcons+ {i} {•} {∅} = eq₁
                equalNormalFormLcons+ {i} {•} {•} = eq₂
                equalNormalFormLcons+ {i} {•} {l• i₁} = eq₃
                equalNormalFormLcons+ {i} {•} {cons t₂ t₃} = {!!} --≡Trans eq₉ (ap₂ (tlcons i) (equalNormalFormCons+ {t₁ = •} {t₂ = t₂}) refl)
                equalNormalFormLcons+ {i} {•} {lcons i₁ t₂ t₃} = eq₅
                equalNormalFormLcons+ {i} {l• i₁} {∅} = refl
                equalNormalFormLcons+ {i} {l• i₁} {•} = eq₇
                equalNormalFormLcons+ {i} {l• i₁} {l• i₂} = refl
                equalNormalFormLcons+ {i} {l• i₁} {cons t₂ t₃} = ≡Trans eq₉ (ap₂ (tlcons i) (equalNormalFormCons+ {t₁ = l• i₁} {t₂ = t₂}) refl)
                equalNormalFormLcons+ {i} {l• i₁} {lcons i₂ t₂ t₃} = refl
                equalNormalFormLcons+ {i} {cons t₁ t₃} {∅} = refl
                equalNormalFormLcons+ {i} {cons t₁ t₃} {•} = eq₄
                equalNormalFormLcons+ {i} {cons t₁ t₃} {l• i₁} = refl
                equalNormalFormLcons+ {i} {cons t₁ t₃} {cons t₂ t₄} = ≡Trans eq₉ (ap₂ (tlcons i) (equalNormalFormCons+ {t₁ = cons t₁ t₃} {t₂ = t₂}) refl)
                equalNormalFormLcons+ {i} {cons t₁ t₃} {lcons i₁ t₂ t₄} = refl
                equalNormalFormLcons+ {i} {lcons i₁ t₁ t₃} {∅} = refl
                equalNormalFormLcons+ {i} {lcons i₁ t₁ t₃} {•} = eq₈
                equalNormalFormLcons+ {i} {lcons i₁ t₁ t₃} {l• i₂} = refl
                equalNormalFormLcons+ {i} {lcons i₁ t₁ t₃} {cons t₂ t₄} = ≡Trans eq₉ (ap₂ (tlcons i) (equalNormalFormCons+ {t₁ = lcons i₁ t₁ t₃} {t₂ = t₂}) refl)
                equalNormalFormLcons+ {i} {lcons i₁ t₁ t₃} {lcons i₂ t₂ t₄} = refl
  
                equalNormalForm+ : {t : Ltree+} → elimLtree+ t ≡ elimLtree+ (normalForm+ t)
                equalNormalForm+ {∅} = refl
                equalNormalForm+ {•} = refl
                equalNormalForm+ {l• i} = refl
                equalNormalForm+ {cons t₁ t₂} = ≡Trans {y = tcons (elimLtree+ (normalForm+ t₁)) (elimLtree+ (normalForm+ t₂))}
                                                  (ap₂ tcons (equalNormalForm+ {t₁}) (equalNormalForm+{t₂}))
                                                  (equalNormalFormCons+ {normalForm+ t₁} {normalForm+ t₂})
                equalNormalForm+ {lcons i t₁ t₂} = ≡Trans {y = tlcons i (elimLtree+ (normalForm+ t₁)) (elimLtree+ (normalForm+ t₂))}
                                                     (ap₂ (tlcons i) (equalNormalForm+ {t₁}) (equalNormalForm+ {t₂}))
                                                     (equalNormalFormLcons+ {i} {normalForm+ t₁} {normalForm+ t₂})

{-
module _ {k} {A : Set k} (t∅ : A) (t• : A) (tl• : I → A) (tcons : A → A → A) (tlcons : I → A → A → A)
         (tt∅ : A) (tt• : A) (ttcons : A → A → A) where
      
   elimLtree : Ltree → A
   elimLtree ∅ = tt∅
   elimLtree • = tt•
   elimLtree (cons t₁ t₂) = ttcons (elimLtree+ t₁) (elimLtree+ t₂)
-}

--                  module _ where

--                    equalNormalCons : {t₁ t₂ : Ltree+} → elimLtree (cons t₁ t₂) ≡ elimLtree (normalFormCons t₁ t₂)
  --                  equalNormalCons = {!!}


--we give a full version when they ignore label
module _ {k} {A : Set k} (t∅ : A) (t• : A) (tcons : A → A → A) where

  elimLtree+-NoLabel : Ltree+ → A
  elimLtree+-NoLabel ∅ = t∅
  elimLtree+-NoLabel • = t•
  elimLtree+-NoLabel (l• i) = t•
  elimLtree+-NoLabel (cons t₁ t₂) = tcons (elimLtree+-NoLabel t₁) (elimLtree+-NoLabel t₂)
  elimLtree+-NoLabel (lcons i t₁ t₂) = tcons (elimLtree+-NoLabel t₁) (elimLtree+-NoLabel t₂)

  elimLtree-NoLabel : Ltree → A
  elimLtree-NoLabel ∅ = t∅
  elimLtree-NoLabel • = t•
  elimLtree-NoLabel (cons t₁ t₂) = tcons (elimLtree+-NoLabel t₁) (elimLtree+-NoLabel t₂)

  normalFormElimNoLabel : (eq₁ : {a : A} → tcons a t• ≡ a)
                          (eq₂ : {a : A} → tcons t• a ≡ a)
                          (eq₃ : {a b c : A} → tcons a (tcons b c) ≡ tcons (tcons a b) c)
                          → {t : Ltree} → elimLtree-NoLabel t ≡ elimLtree-NoLabel (normalForm t)
  normalFormElimNoLabel = {!!}
                


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

Arity : Ltree → ℕ
Arity = elimLtree-NoLabel (s O) O (_+_)

QArity : Qtree → ℕ
QArity = QtreeRec Arity (λ {t} → normalFormElimNoLabel (s O) O (_+_)
                                                       +O
                                                       refl
                                                       (λ {a b c} → ≡Sym (+Assoc {a} {b} {c})) {t})
                        {!!}
                        {!!}


