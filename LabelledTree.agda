module LabelledTree where


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


--Output the normal form of a tree with labels at the root
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








--Now we need lemma to help show that f normalForm t ≡ f t for f inductively define

module _ {k} {A : Set k} (t∅ : A) (t• : A) (tl• : I → A) (tcons : A → A → A) (tlcons : I → A → A → A) where

  elimLtree+ : Ltree+ → A
  elimLtree+ ∅ = t∅
  elimLtree+ • = t•
  elimLtree+ (l• i) = tl• i
  elimLtree+ (cons t₁ t₂) = tcons (elimLtree+ t₁) (elimLtree+ t₂)
  elimLtree+ (lcons i t₁ t₂) = tlcons i (elimLtree+ t₁) (elimLtree+ t₂)

  module _ (eq₁ : (t : Ltree+) → tcons (elimLtree+ t) t• ≡ elimLtree+ t)
           (eq₂ : (t : Ltree+) → tcons t• (elimLtree+ t) ≡ elimLtree+ t)
           (eq₃ : (t₁ t₂ t₃ : Ltree+) → tcons (elimLtree+ t₁) (tcons (elimLtree+ t₂) (elimLtree+ t₃))
                                      ≡ tcons (tcons (elimLtree+ t₁) (elimLtree+ t₂)) (elimLtree+ t₃)) where


         equalNormalFormCons+ : (t₁ t₂ : Ltree+) → elimLtree+ (cons t₁ t₂) ≡ elimLtree+ (normalFormCons+ t₁ t₂)
         
         equalNormalFormCons+ ∅ ∅ = refl
         equalNormalFormCons+ ∅ • = eq₁ ∅
         equalNormalFormCons+ ∅ (l• i) = refl
         equalNormalFormCons+ ∅ (cons t₂ t₃) = ≡Trans (eq₃ ∅ t₂ t₃) (ap₂ tcons (equalNormalFormCons+ ∅ t₂) refl)
         equalNormalFormCons+ ∅ (lcons i t₂ t₃) = refl
         equalNormalFormCons+ • ∅ = eq₂ ∅
         equalNormalFormCons+ • • = eq₂ •
         equalNormalFormCons+ • (l• i) = eq₂ (l• i)
         equalNormalFormCons+ • (cons t₂ t₃) = eq₂ (cons t₂ t₃)
         equalNormalFormCons+ • (lcons i t₂ t₃) = eq₂ (lcons i t₂ t₃)
         equalNormalFormCons+ (l• i) ∅ = refl
         equalNormalFormCons+ (l• i) • = eq₁ (l• i)
         equalNormalFormCons+ (l• i) (l• i₁) = refl
         equalNormalFormCons+ (l• i) (cons t₂ t₃) =  ≡Trans (eq₃ (l• i) t₂ t₃) (ap₂ tcons (equalNormalFormCons+ (l• i) t₂) refl)
         equalNormalFormCons+ (l• i) (lcons i₁ t₂ t₃) = refl
         equalNormalFormCons+ (cons t₁ t₃) ∅ = refl
         equalNormalFormCons+ (cons t₁ t₃) • = eq₁ (cons t₁ t₃)
         equalNormalFormCons+ (cons t₁ t₃) (l• i) = refl
         equalNormalFormCons+ (cons t₁ t₃) (cons t₂ t₄) =  ≡Trans (eq₃ (cons t₁ t₃) t₂ t₄) (ap₂ tcons (equalNormalFormCons+ (cons t₁ t₃) t₂) refl)
         equalNormalFormCons+ (cons t₁ t₃) (lcons i t₂ t₄) = refl
         equalNormalFormCons+ (lcons i t₁ t₃) ∅ = refl
         equalNormalFormCons+ (lcons i t₁ t₃) • = eq₁ (lcons i t₁ t₃)
         equalNormalFormCons+ (lcons i t₁ t₃) (l• i₁) = refl
         equalNormalFormCons+ (lcons i t₁ t₃) (cons t₂ t₄) =  ≡Trans (eq₃ (lcons i t₁ t₃) t₂ t₄) (ap₂ tcons (equalNormalFormCons+ (lcons i t₁ t₃) t₂) refl)
         equalNormalFormCons+ (lcons i t₁ t₃) (lcons i₁ t₂ t₄) = refl

         module _ (eq₄ : {i : I} (t₁ : Ltree+) → tlcons i (elimLtree+ t₁) t• ≡ elimLtree+ (addLbl+ i t₁))
                  (eq₅ : {i : I} (t₂ : Ltree+) → tlcons i t• (elimLtree+ t₂) ≡ elimLtree+ (addLbl+ i t₂))
                  (eq₆ : {i : I} (t₁ t₂ t₃ : Ltree+) → tlcons i (elimLtree+ t₁) (tcons (elimLtree+ t₂) (elimLtree+ t₃))
                                                     ≡ tlcons i (tcons (elimLtree+ t₁) (elimLtree+ t₂)) (elimLtree+ t₃)) where


                equalNormalFormLcons+ : {i : I} (t₁ t₂ : Ltree+) → elimLtree+ (lcons i t₁ t₂) ≡ elimLtree+ (normalFormLcons+ i t₁ t₂)
                
                equalNormalFormLcons+ ∅ ∅ = refl
                equalNormalFormLcons+ ∅ • = eq₄ ∅
                equalNormalFormLcons+ ∅ (l• i) = refl
                equalNormalFormLcons+ ∅ (cons t₂ t₃) = ≡Trans (eq₆ ∅ t₂ t₃)
                                                              (ap₂ (tlcons _) (equalNormalFormCons+ ∅ t₂) refl)
                equalNormalFormLcons+ ∅ (lcons i t₂ t₃) = refl
                equalNormalFormLcons+ • ∅ = eq₅ ∅
                equalNormalFormLcons+ • • = eq₅ •
                equalNormalFormLcons+ • (l• i) = eq₅ (l• i)
                equalNormalFormLcons+ • (cons t₂ t₃) = eq₅ (cons t₂ t₃)
                equalNormalFormLcons+ • (lcons i t₂ t₃) = eq₅ (lcons i t₂ t₃)
                equalNormalFormLcons+ (l• i) ∅ = refl
                equalNormalFormLcons+ (l• i) • = eq₄ (l• i)
                equalNormalFormLcons+ (l• i) (l• j) = refl
                equalNormalFormLcons+ (l• i) (cons t₂ t₃) = ≡Trans (eq₆ (l• i) t₂ t₃)
                                                                   (ap₂ (tlcons _) (equalNormalFormCons+ (l• i) t₂) refl)
                equalNormalFormLcons+ (l• i) (lcons i₁ t₂ t₃) = refl
                equalNormalFormLcons+ (cons t₁ t₃) ∅ = refl
                equalNormalFormLcons+ (cons t₁ t₃) • = eq₄ (cons t₁ t₃)
                equalNormalFormLcons+ (cons t₁ t₃) (l• i) = refl
                equalNormalFormLcons+ (cons t₁ t₃) (cons t₂ t₄) = ≡Trans (eq₆ (cons t₁ t₃) t₂ t₄)
                                                                         (ap₂ (tlcons _) (equalNormalFormCons+ (cons t₁ t₃) t₂) refl)
                equalNormalFormLcons+ (cons t₁ t₃) (lcons i t₂ t₄) = refl
                equalNormalFormLcons+ (lcons i t₁ t₃) ∅ = refl
                equalNormalFormLcons+ (lcons i t₁ t₃) • = eq₄ (lcons i t₁ t₃)
                equalNormalFormLcons+ (lcons i t₁ t₃) (l• i₁) = refl
                equalNormalFormLcons+ (lcons i t₁ t₃) (cons t₂ t₄) = ≡Trans (eq₆ (lcons i t₁ t₃) t₂ t₄)
                                                                            (ap₂ (tlcons _) (equalNormalFormCons+ (lcons i t₁ t₃) t₂) refl)
                equalNormalFormLcons+ (lcons i t₁ t₃) (lcons i₁ t₂ t₄) = refl
  
                equalNormalForm+ : (t : Ltree+) → elimLtree+ t ≡ elimLtree+ (normalForm+ t)
                equalNormalForm+ ∅ = refl
                equalNormalForm+ • = refl
                equalNormalForm+ (l• i) = refl
                equalNormalForm+ (cons t₁ t₂) = ≡Trans {y = tcons (elimLtree+ (normalForm+ t₁)) (elimLtree+ (normalForm+ t₂))}
                                                  (ap₂ tcons (equalNormalForm+ t₁) (equalNormalForm+ t₂))
                                                  (equalNormalFormCons+ (normalForm+ t₁) (normalForm+ t₂))
                equalNormalForm+ (lcons i t₁ t₂) = ≡Trans {y = tlcons i (elimLtree+ (normalForm+ t₁)) (elimLtree+ (normalForm+ t₂))}
                                                     (ap₂ (tlcons i) (equalNormalForm+ t₁) (equalNormalForm+ t₂))
                                                     (equalNormalFormLcons+ (normalForm+ t₁) (normalForm+ t₂))




module _  {k} {A : Set k} (t∅ : A) (t• : A) (tl• : I → A) (tcons : A → A → A) (tlcons : I → A → A → A)
          (tt∅ : A) (tt• : A) (ttcons : A → A → A) where

       elimLtreeAux = elimLtree+ t∅ t• tl• tcons tlcons

       elimLtree : Ltree → A
       elimLtree ∅ = tt∅
       elimLtree • = tt•
       elimLtree (cons t₁ t₂) = ttcons (elimLtreeAux t₁) (elimLtreeAux t₂)

       module _ (eq₁ : (t : Ltree+) → tcons (elimLtreeAux t) t• ≡ elimLtreeAux t)
                (eq₂ : (t : Ltree+) → tcons t• (elimLtreeAux t) ≡ elimLtreeAux t)
                (eq₃ : (t₁ t₂ t₃ : Ltree+) → tcons (elimLtreeAux t₁) (tcons (elimLtreeAux t₂) (elimLtreeAux t₃))
                                      ≡ tcons (tcons (elimLtreeAux t₁) (elimLtreeAux t₂)) (elimLtreeAux t₃))
                (eq₄ : {i : I} (t₁ : Ltree+) → tlcons i (elimLtreeAux t₁) t• ≡ elimLtreeAux (addLbl+ i t₁))
                (eq₅ : {i : I} (t₂ : Ltree+) → tlcons i t• (elimLtreeAux t₂) ≡ elimLtreeAux (addLbl+ i t₂))
                (eq₆ : {i : I} (t₁ t₂ t₃ : Ltree+) → tlcons i (elimLtreeAux t₁) (tcons (elimLtreeAux t₂) (elimLtreeAux t₃))
                                                     ≡ tlcons i (tcons (elimLtreeAux t₁) (elimLtreeAux t₂)) (elimLtreeAux t₃))
                (eq₇ : (t₁ : Ltree+) → ttcons (elimLtreeAux t₁) t• ≡ elimLtree (forgetLbl t₁))
                (eq₈ : (t₂ : Ltree+) → ttcons t• (elimLtreeAux t₂) ≡ elimLtree (forgetLbl t₂))
                (eq₉ : (t₁ t₂ t₃ : Ltree+) → ttcons (elimLtreeAux t₁) (tcons (elimLtreeAux t₂) (elimLtreeAux t₃))
                                           ≡ ttcons (tcons (elimLtreeAux t₁) (elimLtreeAux t₂)) (elimLtreeAux t₃)) where


              equalCons+ = equalNormalFormCons+ t∅ t• tl• tcons tlcons eq₁ eq₂ eq₃

              equal+ = equalNormalForm+ t∅ t• tl• tcons tlcons eq₁ eq₂ eq₃ eq₄ eq₅ eq₆


              equalNormalFormCons : (t₁ t₂ : Ltree+) → elimLtree (cons t₁ t₂) ≡ elimLtree (normalFormCons t₁ t₂)

              equalNormalFormCons ∅ ∅ = refl
              equalNormalFormCons ∅ • = eq₇ ∅
              equalNormalFormCons ∅ (l• i) = refl
              equalNormalFormCons ∅ (cons t₂ t₃) = ≡Trans (eq₉ ∅ t₂ t₃)
                                                          (ap₂ ttcons (equalCons+ ∅ t₂) refl) 
              equalNormalFormCons ∅ (lcons i t₂ t₃) = refl
              equalNormalFormCons • ∅ = eq₈ ∅
              equalNormalFormCons • • = eq₈ •
              equalNormalFormCons • (l• i) = eq₈ (l• i)
              equalNormalFormCons • (cons t₂ t₃) = eq₈ (cons t₂ t₃)
              equalNormalFormCons • (lcons i t₂ t₃) = eq₈ (lcons i t₂ t₃)
              equalNormalFormCons (l• i) ∅ = refl
              equalNormalFormCons (l• i) • = eq₇ (l• i)
              equalNormalFormCons (l• i) (l• i₁) = refl
              equalNormalFormCons (l• i) (cons t₂ t₃) =  ≡Trans (eq₉ (l• i) t₂ t₃)
                                                                (ap₂ ttcons (equalCons+ (l• i) t₂) refl) 
              equalNormalFormCons (l• i) (lcons i₁ t₂ t₃) = refl
              equalNormalFormCons (cons t₁ t₃) ∅ = refl
              equalNormalFormCons (cons t₁ t₃) • = eq₇ (cons t₁ t₃)
              equalNormalFormCons (cons t₁ t₃) (l• i) = refl
              equalNormalFormCons (cons t₁ t₃) (cons t₂ t₄) =  ≡Trans (eq₉ (cons t₁ t₃) t₂ t₄)
                                                                      (ap₂ ttcons (equalCons+ (cons t₁ t₃) t₂) refl) 
              equalNormalFormCons (cons t₁ t₃) (lcons i t₂ t₄) = refl
              equalNormalFormCons (lcons i t₁ t₃) ∅ = refl
              equalNormalFormCons (lcons i t₁ t₃) • = eq₇ (lcons i t₁ t₃)
              equalNormalFormCons (lcons i t₁ t₃) (l• i₁) = refl
              equalNormalFormCons (lcons i t₁ t₃) (cons t₂ t₄) =  ≡Trans (eq₉ (lcons i t₁ t₃) t₂ t₄)
                                                                         (ap₂ ttcons (equalCons+ (lcons i t₁ t₃) t₂) refl) 
              equalNormalFormCons (lcons i t₁ t₃) (lcons i₁ t₂ t₄) = refl

              equalNormalForm : (t : Ltree) → elimLtree t ≡ elimLtree (normalForm t)
              equalNormalForm ∅ = refl
              equalNormalForm • = refl
              equalNormalForm (cons t₁ t₂) = ≡Trans (ap₂ ttcons (equal+ t₁) (equal+ t₂))
                                                    (equalNormalFormCons (normalForm+ t₁) (normalForm+ t₂))



-- We give a lemma useful to show that a function ignoring label pass through quotients

module _ {k} {A : Set k} (t∅ : A) (t• : A) (tcons : A → A → A) where


  elimLtree-NoLabel+ : Ltree+ → A
  elimLtree-NoLabel+ = elimLtreeAux t∅ t• (λ _ → t•) tcons (λ _ → tcons) t∅ t• tcons

  elimLtree-NoLabel : Ltree → A
  elimLtree-NoLabel = elimLtree t∅ t• (λ _ → t•) tcons (λ _ → tcons) t∅ t• tcons



  --We show that elimLtree-NoLabel is preserve by grafting with label i

  elimLtreeGraft•-NoLabel+ :  {i : I} {t : Ltree+} → (a : arity+ t)
                              → elimLtree-NoLabel+ (graft+ t a (l• i)) ≡ elimLtree-NoLabel+ (graft+ t a •)
                              
  elimLtreeGraft•-NoLabel+ ar∅+ = refl
  elimLtreeGraft•-NoLabel+ (arConsL+ a) = ap₂ tcons (elimLtreeGraft•-NoLabel+ a) refl
  elimLtreeGraft•-NoLabel+ (arConsR+ a) = ap₂ tcons refl (elimLtreeGraft•-NoLabel+ a)
  elimLtreeGraft•-NoLabel+ (arlConsL+ a) = ap₂ tcons (elimLtreeGraft•-NoLabel+ a) refl
  elimLtreeGraft•-NoLabel+ (arlConsR+ a) = ap₂ tcons refl (elimLtreeGraft•-NoLabel+ a)
  
  
  elimLtreeGraft•-NoLabel : {i : I} {t : Ltree} → (a : arity t)
                            → elimLtree-NoLabel (graft t a (l• i)) ≡ elimLtree-NoLabel (graft t a •)
                            
  elimLtreeGraft•-NoLabel ar∅ = refl
  elimLtreeGraft•-NoLabel (arConsL a) = ap₂ tcons (elimLtreeGraft•-NoLabel+ a) refl
  elimLtreeGraft•-NoLabel (arConsR a) = ap₂ tcons refl (elimLtreeGraft•-NoLabel+ a)
  

  elimLtreeGraftCons-NoLabel+ :  {i : I} {t : Ltree+} → (a : arity+ t) {t₁ t₂ : Ltree+}
                                 → elimLtree-NoLabel+ (graft+ t a (lcons i t₁ t₂)) ≡ elimLtree-NoLabel+ (graft+ t a (cons t₁ t₂))
                                 
  elimLtreeGraftCons-NoLabel+ ar∅+ = refl
  elimLtreeGraftCons-NoLabel+ (arConsL+ a) = ap₂ tcons (elimLtreeGraftCons-NoLabel+ a) refl
  elimLtreeGraftCons-NoLabel+ (arConsR+ a) = ap₂ tcons refl (elimLtreeGraftCons-NoLabel+ a)
  elimLtreeGraftCons-NoLabel+ (arlConsL+ a) = ap₂ tcons (elimLtreeGraftCons-NoLabel+ a) refl
  elimLtreeGraftCons-NoLabel+ (arlConsR+ a) = ap₂ tcons refl (elimLtreeGraftCons-NoLabel+ a)

  elimLtreeGraftCons-NoLabel : {i : I} {t : Ltree} → (a : arity t) → {t₁ t₂ : Ltree+}
                               → elimLtree-NoLabel (graft t a (lcons i t₁ t₂)) ≡  elimLtree-NoLabel (graft t a (cons t₁ t₂))
  elimLtreeGraftCons-NoLabel ar∅ = refl
  elimLtreeGraftCons-NoLabel (arConsL a) = ap₂ tcons (elimLtreeGraftCons-NoLabel+ a) refl
  elimLtreeGraftCons-NoLabel (arConsR a) = ap₂ tcons refl (elimLtreeGraftCons-NoLabel+ a)


  --Now we show a condition for elimLtree-NoLabel to be invariant by normalisation of tree

  module _ (eq₁ : {a : A} → tcons a t• ≡ a)
           (eq₂ : {a : A} → tcons t• a ≡ a)
           (eq₃ : {a b c : A} → tcons a (tcons b c) ≡ tcons (tcons a b) c) where

         normalFormElimNoLabel : {t : Ltree} → elimLtree-NoLabel t ≡ elimLtree-NoLabel (normalForm t)
                          
         normalFormElimNoLabel {t} = equalNormalForm t∅ t• (λ _ → t•) tcons (λ _ → tcons) t∅ t• tcons
                                                     (λ _ → eq₁)
                                                     (λ t₁ → eq₂)
                                                     (λ t₁ t₂ t₃ → eq₃)
                                                     (λ { ∅ → eq₁ ; • → eq₁ ; (l• i) → eq₁ ; (cons t₁ t₂) → eq₁ ; (lcons i t₁ t₂) → eq₁})
                                                     (λ { ∅ → eq₂ ; • → eq₂ ; (l• i) → eq₂ ; (cons t₂ t₃) → eq₂ ; (lcons i t₂ t₃) → eq₂})
                                                     (λ t₁ t₂ t₃ → eq₃)
                                                     (λ { ∅ → eq₁ ; • → eq₁ ; (l• i) → eq₁ ; (cons t₁ t₂) → eq₁ ; (lcons i t₁ t₂) → eq₁})
                                                     (λ { ∅ → eq₂ ; • → eq₂ ; (l• i) → eq₂ ; (cons t₂ t₃) → eq₂ ; (lcons i t₂ t₃) → eq₂})
                                                     (λ t₁ t₂ t₃ → eq₃) t
                


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


