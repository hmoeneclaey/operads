{-# OPTIONS --no-eta-equality #-}
{-# OPTIONS --rewriting #-}

module LoopSpace where

open import Agda.Primitive
open import Data
open import FibrantUniverse
open import FiniteSet
open import MorphismFiniteSet
open import Operad
open import Cofibration
open import FiniteSet2



--Some auxiliary lemma

∨NatId : ∀ {k l} {A : Set k} {B : Set l} {x : A ∨ B} → ∨Nat Id Id x ≡ x
∨NatId {x = left x} = refl
∨NatId {x = right x} = refl



--We define string of composable paths

record composablePath {k} (X : Set k) (A : Set) {{_ : FOSet A}} : Set k where
  field
    point : Succ A → X
    path : (a : A) → point (inc₀ a) ~~> point (inc₁ a)


module _ {k} {X : Set k} {A : Set} {{_ : FOSet A}} where


  ≡ComposablePathAux2 : {P Q : composablePath X A}
                       → composablePath.point P ≡ composablePath.point Q
                       → ((a : A) (i : I) → composablePath.path P a $ i ≡ composablePath.path Q a $ i)
                       → P ≡ Q
                     
  ≡ComposablePathAux2 {P = record { point = f ; path = F }} {Q = record { point = g ; path = G }} refl eqPath = ap (λ H → record { point = f ; path = H })
                                                                                                 (funext (λ a → ≡Path (eqPath a)))


  ≡ComposablePathAux1 : {P Q : composablePath X A}
                    → ((a : Succ A) → composablePath.point P a ≡ composablePath.point Q a)
                    → ((a : A) (i : I) → composablePath.path P a $ i ≡ composablePath.path Q a $ i)
                    → P ≡ Q
                  
  ≡ComposablePathAux1 eqPoint eqPath = ≡ComposablePathAux2 (funext eqPoint) eqPath


  ≡ComposablePath :  {P Q : composablePath X A}
                     → composablePath.point P max ≡ composablePath.point Q max
                    → ((a : A) (i : I) → composablePath.path P a $ i ≡ composablePath.path Q a $ i)
                    → P ≡ Q

  ≡ComposablePath {P} {Q} eqPoint eqPath = ≡ComposablePathAux1 (λ { (left a) → ≡Trans {y = composablePath.path P a $ e₀}
                                                                              (≡Sym (eqe₀ (composablePath.path P a)))
                                                                              (≡Trans (eqPath a e₀)
                                                                                      (eqe₀ (composablePath.path Q a))) ;
                                                                    (right *) → eqPoint}) eqPath


  firstPoint : composablePath X A → X
  firstPoint p = composablePath.point p min

  lastPoint : composablePath X A → X
  lastPoint p = composablePath.point p max

  composableHrefl : X → composablePath X A
  composableHrefl x = record { point = λ _ → x ; path = λ _ → hrefl }

  loopComposable : {x : X} → (A → x ~~> x) → composablePath X A
  loopComposable {x = x} f = record { point = λ _ → x ; path = f }


module _ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {B : A → Set} {{_ : {a : A} → FOSet (B a)}} where

  ΣComposablePath : (a : A) → composablePath X (Σ A B) → composablePath X (B a)
  ΣComposablePath a record { point = f ; path = F }
                    = record { point = f o ΣSuccInc a ;
                               path = λ b → endpointPath (F (a , b)) refl (ap f ΣSuccIncInc₁) }

  ΣComposablePathHrefl : {a : A} {x : X} → ΣComposablePath a (composableHrefl x) ≡ composableHrefl x
  ΣComposablePathHrefl = ≡ComposablePath refl (λ _ _ → refl)

  

--Now we show functoriality of the strings of composable paths

module _ {k} {X : Set k} where

  composablePathFunct : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}}
                        (f : A → B) → HomFO f → composablePath X B → composablePath X A
                        
  composablePathFunct f homf record { point = g ;
                                      path = G }
                           = record { point = g o ∨Nat f Id ;
                                      path = λ a → endpointPath (G (f a)) refl (ap g (inc₁morphism f homf)) }


  composablePathFunctId : {A : Set} {{_ : FOSet A}} {a : composablePath X A}
                          → composablePathFunct Id HomFOId a ≡ a
                        
  composablePathFunctId {a = record { point = f ; path = F }} = ≡ComposablePath refl (λ _ _ → refl)


  composablePathFunctComp : {A B C : Set} {{_ : FOSet A}} {{_ : FOSet B}} {{_ : FOSet C}}
                            {f : A → B} {g : B → C} (homf : HomFO f) (homg : HomFO g) (c : composablePath X C)
                            → composablePathFunct f homf (composablePathFunct g homg c) ≡ composablePathFunct (g o f) (HomFOComp homf homg) c

  composablePathFunctComp homf homg record { point = h ; path = H } = ≡ComposablePath refl (λ _ _ → refl)

 

module _ {k} {X : Set k} {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}}
         (f : A → B) (homf : HomFO f) where

       composablePathFunctFirstPoint : (p : composablePath X B) → firstPoint (composablePathFunct f homf p) ≡ firstPoint p
       composablePathFunctFirstPoint record { point = g ; path = G } = ap g (minMorphism f homf)

       composablePathFunctLastPoint : (p : composablePath X B) → lastPoint (composablePathFunct f homf p) ≡ lastPoint p
       composablePathFunctLastPoint record { point = g ; path = G } = refl 

       composablePathFunctHrefl : {x : X} → composablePathFunct f homf (composableHrefl x) ≡ composableHrefl x
       composablePathFunctHrefl = ≡ComposablePath refl (λ _ _ → refl)

       loopComposableFunct : {x : X} {a : B → x ~~> x} → composablePathFunct f homf (loopComposable a) ≡ loopComposable (a o f)
       loopComposableFunct {a = a} = ≡ComposablePath refl (λ _ _ → refl)


--We define the path operad

module _ {k} (X : Set k) where

  record PathOp (A : Set) {{_ : FOSet A}} : Set k where
    field
      fun : (p : composablePath X A) → firstPoint p ~~> lastPoint p
      equality : (x : X) → fun (composableHrefl x) ≡ hrefl


≡PathOpAux : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {P Q : PathOp X A}
          → PathOp.fun P ≡ PathOp.fun Q → P ≡ Q
          
≡PathOpAux {P = record { fun = ϕ ; equality = eqϕ }} {record { fun = ψ ; equality = eqψ }} refl
           = ap (λ H → record { fun = ϕ ; equality = H }) (funext (λ _ → UIP)) 


≡PathOp : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {P Q : PathOp X A}
          → ((p : composablePath X A) → PathOp.fun P p ≡ PathOp.fun Q p) → P ≡ Q
          
≡PathOp equalFun = ≡PathOpAux (funext equalFun)



--An auxiliary result

≡depFunction : ∀ {k l m} {A₁ : Set k} {A₂ : Set l} {h : A₁ → A₂} {B : A₂ → Set m} {f : (a₁ : A₁) → B (h a₁)}
               {a₁ a₂ : A₁} {a₃ : A₂} (p : h a₁ ≡ a₃) (q : h a₂ ≡ a₃) (r : a₁ ≡ a₂) → transport B p (f a₁) ≡ transport B q (f a₂)
≡depFunction refl refl refl = refl



--We define family with J eliminator, so that we can show composable paths form such a family

record Family {k} (X : Set k) : Set (lsuc k) where
  constructor _::_
  field
    obj : Set k
    point : X → obj


module _ {k} {X : Set k} where


  record _≅Family_ (P₁ : Family X) (P₂ : Family X) : Set k where
    field
      mapFam : Family.obj P₁ → Family.obj P₂
      isoMapFam : iso mapFam
      pointFam : (x : X) → mapFam (Family.point P₁ x) ≡ Family.point P₂ x


  hasJElim : Family X → Setω
  
  hasJElim (Obj :: Hrefl) = ∀ {l} (C : Obj → Set l) {{_ : {p : Obj} → Fib (C p)}}
                                  (d : (x : X) → C (Hrefl x))
                                  → Σ ((p : Obj) → C p) (λ ϕ → (x : X) → ϕ (Hrefl x) ≡ d x)


  ≅FamilyTrans : {P₁ P₂ P₃ : Family X} → P₁ ≅Family P₂ → P₂ ≅Family P₃ → P₁ ≅Family P₃
  
  ≅FamilyTrans {P₁ :: e₁} {P₂ :: e₂} {P₃ :: e₃}
               record { mapFam = f₁ ;
                        isoMapFam = isof₁ ;
                        pointFam = eqf₁ }
               record { mapFam = f₂ ;
                        isoMapFam = isof₂ ;
                        pointFam = eqf₂ }
             = record { mapFam = f₂ o f₁ ;
                        isoMapFam = isoComp isof₁ isof₂ ;
                        pointFam = λ x → ≡Trans (ap f₂ (eqf₁ x)) (eqf₂ x) }


  ≅hasJElim : {P₁ P₂ : Family X} → P₁ ≅Family P₂ → hasJElim P₁ → hasJElim P₂
  
  ≅hasJElim {P₁ :: e₁} {P₂ :: e₂} record { mapFam = f ;
                                           isoMapFam = record { inv = g ;
                                                                invLeft = gleft ;
                                                                invRight = gright } ;
                                           pointFam = eqf } ElimP₁ C d
                                           
            = let aux = ElimP₁ (C o f) λ x → transport C (≡Sym (eqf x)) (d x) in
              (λ p → transport C (≡Sym (gleft p)) (Σleft aux (g p))) ,
              λ x → ≡Trans (≡depFunction {h = f} {f = Σleft aux} (≡Sym (gleft (e₂ x))) (eqf x)
                                         (isoCancel (record { inv = g ; invLeft = gleft ; invRight = gright })
                                         (≡Trans (≡Sym (gleft (e₂ x)) ) (≡Sym (eqf x)))))
                           (≡Trans (ap (transport C (eqf x)) (Σright aux x))
                                   (transportDouble {p = ≡Sym (eqf x)} {q = eqf x}) )




--We give another equivalent definition of composable paths, as a Family

module _ {k} {X : Set k} {{_ : Fib X}} where

  compPath : ℕ → X → X → Set k
  compPath O x y = x ≡ y
  compPath (s n) x z = Σ X (λ y → compPath n x y ∧ y ~~> z)


  --Some fibrancy results 

  ≅Sing : {y : X} → ⊤ {lzero} ≅ Σ X (λ x → compPath O x y)
  
  ≅Sing {y} = record { isoFun = λ _ → y , refl ;
                       isIso = record { inv = λ _ → * ;
                                        invLeft = λ { (x , refl) → refl} ;
                                        invRight = λ _ → refl } }


  ≅CompPathSucc : {n : ℕ} {z : X} → Σ X (λ y → (Σ X (λ x → compPath n x y)) ∧ y ~~> z) ≅ Σ X (λ x → compPath (s n) x z)
  
  ≅CompPathSucc = record { isoFun = λ { (y , ((x , p) , q)) → x , (y , (p , q))} ;
                           isIso = record { inv = λ { (x , (y , (p , q))) → y , ((x , p) , q)} ;
                                            invLeft = λ { (_ , (_ , (_ , _))) → refl} ;
                                            invRight = λ { (_ , ((_ , _) , _)) → refl} } }


  instance
    FibCompPath : {n : ℕ} {y : X} → Fib (Σ X (λ x → compPath n x y))
    FibCompPath {O} = ≅Fib {X = ⊤ {lzero}} ≅Sing
    FibCompPath {s n} {y} = ≅Fib ≅CompPathSucc


  ≅CompPath : ∀ {k} {n : ℕ} {y : X} {C : {x : X} → (p : compPath n x y) → Set k} →
              ((p : Σ X (λ x → compPath n x y)) → C (Σright p)) ≅ ({x : X} → (p : compPath n x y) → C p)
              
  ≅CompPath = record { isoFun = λ f {x} p → f (x , p) ;
                       isIso = record { inv = λ { f (x , p) → f {x} p} ;
                                        invLeft = λ _ → refl ;
                                        invRight = λ _ → funext (λ { (_ , _) → refl}) } }


  FibCompPathAux : ∀ {k} {n : ℕ} {y : X} {C : {x : X} → compPath n x y → Set k}
                  → {{_ : {x : X} → {p : compPath n x y} → Fib (C p)}} → Fib ({x : X} → (p : compPath n x y) → C p)
                  
  FibCompPathAux = ≅Fib ≅CompPath


  --We define the J-structure on compPath

  Hrefl : {n : ℕ} (x : X) → compPath n x x
  Hrefl {O} x = refl
  Hrefl {s n} x = x , ((Hrefl {n} x) , hrefl)

  JCompPath : ∀ {l} {n : ℕ} (C : {x y : X} → compPath n x y → Set l) {{_ : {x y : X} {p : compPath n x y} → Fib (C p)}}
              (d : (x : X) → C (Hrefl x)) {x y : X} (p : compPath n x y) → C p
  JCompPath {n = O} C d {x} refl = d x
  JCompPath {n = s n} C d (y , (p , q)) = JPath (λ {y} {z} q → {x : X} (p : compPath n x y) → C (y , (p , q)))
                                                {{λ {y} {_} {q} → FibCompPathAux {C = λ {x} p → C (y , (p , q))}}}
                                                (λ x p₁ → JCompPath (λ {x} {y} p₁ → C (y , (p₁ , hrefl))) (λ x₁ → d x₁) p₁) q p

  JCompPathCompute : ∀ {l} {n : ℕ} (C : {x y : X} → compPath n x y → Set l) {{_ : {x y : X} {p : compPath n x y} → Fib (C p)}}
              (d : (x : X) → C (Hrefl x)) {x : X} → JCompPath C d (Hrefl x) ≡ d x
  JCompPathCompute {n = O} C d = refl
  JCompPathCompute {n = s n} C d {x} = JCompPathCompute (λ p₁ → C (_ , (p₁ , hrefl))) d


  --Now we show we indeed have a family compPath with J eliminator

  ObjFamilyCompPath : ℕ → Set k
  ObjFamilyCompPath n = Σ X (λ x → Σ X (λ y → compPath n x y))

  FamilyCompPath : ℕ → Family X
  FamilyCompPath n = ObjFamilyCompPath n :: λ x → x , (x , (Hrefl x))

  hasJElimCompPath : {n : ℕ} → hasJElim (FamilyCompPath n)
  hasJElimCompPath C d = (λ { (x , (y , p)) → JCompPath (λ {x₁} {y₁} p₁ → C (x₁ , (y₁ , p₁))) d p}) ,
                         λ x → JCompPathCompute (λ {x₁} {y₁} p₁ → C (x₁ , (y₁ , p₁))) d



--We show isomorphisms of families composablePath and compPath, using three intermediary isomorphism of families

finc : {n : ℕ} → Fin n → Fin (s n)
finc = Fin⊤SuccAux

module _ {k} {X : Set k} {{_ : Fib X}} where

  --We define the family of composable paths
  
  FamilyComposablePath : (A : Set) {{_ : FOSet A}} → Family X
  FamilyComposablePath A = (composablePath X A) :: composableHrefl

  --We define a family using canoncial finite sets

  record composablePathCanonical (n : ℕ) : Set k where
    field
      point : Fin (s n) → X
      path : (k : Fin (n)) → point (finc k) ~~> point (fsucc k)


  --equality of canonical composable paths

  ≡ComposablePathCanonicalAuxAux : {n : ℕ} {x y : composablePathCanonical n}
                           → composablePathCanonical.point x ≡ composablePathCanonical.point y
                           → ((k : Fin n) (i : I) → composablePathCanonical.path x k $ i ≡ composablePathCanonical.path y k $ i)
                           → x ≡ y

  ≡ComposablePathCanonicalAuxAux {x = record { point = h₁ ; path = H₁ }}
                                 {y = record { point = h₂ ; path = H₂ }} refl Hyp
                               = ap (λ H → record { point = h₁ ; path = H }) (funext (λ a → ≡Path (λ i → Hyp a i)))


  ≡ComposablePathCanonical : {n : ℕ} {x y : composablePathCanonical n}
                           → ((k : Fin (s n)) → composablePathCanonical.point x k ≡ composablePathCanonical.point y k)
                           → ((k : Fin n) (i : I) → composablePathCanonical.path x k $ i ≡ composablePathCanonical.path y k $ i)
                           → x ≡ y
                           
  ≡ComposablePathCanonical Hyp = ≡ComposablePathCanonicalAuxAux (funext (λ a → Hyp a))

{-
  ≡ComposablePathCanonical : {n : ℕ} {x y : composablePathCanonical n}
                           → (composablePathCanonical.point x fmax ≡ composablePathCanonical.point y fmax)
                           → ((k : Fin n) (i : I) → composablePathCanonical.path x k $ i ≡ composablePathCanonical.path y k $ i)
                           → x ≡ y
                           
  ≡ComposablePathCanonical Hyp₁ Hyp₂ = ≡ComposablePathCanonicalAux {!!} Hyp₂
-}

  composableHreflCanonical : {n : ℕ} → X → composablePathCanonical n
  composableHreflCanonical x = record { point = λ _ → x ; path = λ _ → hrefl }

  FamilyComposablePathCanonical : (n : ℕ) → Family X
  FamilyComposablePathCanonical n = (composablePathCanonical n) :: composableHreflCanonical


  --First isomorphism between family

  compPathFun : {n : ℕ} → ObjFamilyCompPath {X = X} n → composablePathCanonical n
  compPathFun = {!!}

  ≅CompPathCanonical₁ : {n : ℕ} → FamilyCompPath n ≅Family FamilyComposablePathCanonical n
  
  ≅CompPathCanonical₁ = {!!}


  --Some auxialiary lemmas

  Fin⊤SuccInc₁ : {n : ℕ} {k : Fin n} → fsucc k ≡ Fin⊤Succ (inc₁ k)
  Fin⊤SuccInc₁ {k = k} = ≡Trans {y = Fin⊤Succ (invFin⊤Succ (fsucc k))}
                                (Fin⊤SuccInvLeft (fsucc k))
                                (ap Fin⊤Succ (≡Sym (∨NatId {x = invFin⊤Succ (fsucc k)})))

  InvFin⊤SuccInc₁ : {n : ℕ} {k : Fin n} → inc₁ k ≡ invFin⊤Succ (fsucc k)
  InvFin⊤SuccInc₁ {k = k} = isoCancel isoFin⊤Succ
                            (≡Trans (≡Sym (Fin⊤SuccInc₁ {k = k}))
                                    (Fin⊤SuccInvLeft (fsucc k)))

  InvFin⊤SuccInc₀ : {n : ℕ} {k : Fin n} → inc₀ k ≡ invFin⊤Succ (finc k)
  InvFin⊤SuccInc₀ {k = fzero} = refl
  InvFin⊤SuccInc₀ {k = fsucc k} = (ap (∨Nat fsucc Id) (InvFin⊤SuccInc₀ {k = k})) 


  --Second isomorphism between family

  ≅CompPathCanonical₂ : {n : ℕ} → FamilyComposablePathCanonical n ≅Family (FamilyComposablePath (Fin n))
  
  ≅CompPathCanonical₂ {n} = record { mapFam = λ { record { point = f ;
                                                           path = F }
                                                → record { point = f o Fin⊤Succ ;
                                                           path = λ k → endpointPath (F k)
                                                                        refl (ap f Fin⊤SuccInc₁) }} ;
                                     isoMapFam = record { inv = λ { record { point = f ;
                                                                             path = F }
                                                                  → record { point = f o invFin⊤Succ ;
                                                                             path = λ k₁ → endpointPath (F k₁)
                                                                                           (ap f InvFin⊤SuccInc₀) (ap f InvFin⊤SuccInc₁) }} ;
                                                          invLeft = λ { record { point = f ; path = F }
                                                                      → ≡ComposablePath (ap f (Fin⊤SuccInvRight max))
                                                                                        (λ _ _ → refl)} ;
                                                          invRight = λ { record { point = f ; path = F }
                                                                       → ≡ComposablePathCanonical (λ _ → ap f (Fin⊤SuccInvLeft _))
                                                                                                  λ _ _ → refl} } ;
                                     pointFam = λ x → ≡ComposablePath refl (λ _ _ → refl) }


  module _ {A : Set} {{_ : FOSet A}} where

    --Third isomorphism between families

    ≅ComposablePathCanonical : FamilyComposablePath (Fin (cardinal {A})) ≅Family (FamilyComposablePath A)
    
    ≅ComposablePathCanonical = let f = funFO {A} in
                               let isof = isIsoFO {A} in
                               let g = iso.inv isof in
                               record { mapFam = λ { record { point = h ;
                                                              path = H }
                                                   → record { point = h o SuccNat f ;
                                                              path = λ a → endpointPath (H (f a))
                                                                           refl (ap h (inc₁morphism f HomFOcanonical)) }} ;
                                        isoMapFam = record { inv = λ { record { point = h ;
                                                                                path = H }
                                                                     → record { point = h o SuccNat g ;
                                                                                path = λ a → endpointPath (H (g a))
                                                                                       refl (ap h (inc₁morphism g HomFOcanonicalInv)) }} ;
                                                             invLeft = λ { record { point = h ; path = H }
                                                                         → ≡ComposablePath refl (λ a i → ap (λ a₁ → H a₁ $ i) (iso.invRight isof a))} ;
                                                             invRight = λ { record { point = h ; path = H }
                                                                          → ≡ComposablePath refl (λ a i → ap (λ a₁ → H a₁ $ i) (iso.invLeft isof a))} } ;
                                        pointFam = λ x → ≡ComposablePath refl (λ _ _ → refl) }


    --main isomorphism between families

    ≅CompComposablePath : FamilyCompPath (cardinal {A}) ≅Family (FamilyComposablePath A)
    
    ≅CompComposablePath = ≅FamilyTrans (≅FamilyTrans ≅CompPathCanonical₁ ≅CompPathCanonical₂) ≅ComposablePathCanonical 

 



--In this module we show PathOp strongly contractible


module _ {k} {X : Set k} {{_ : Fib X}} {A : Set} {{_ : FOSet A}} where


  --First the elimination principle for composablePath, deduced from the one on CompPath

  hasElimComposablePath : hasJElim (FamilyComposablePath {X = X} A)
  hasElimComposablePath = ≅hasJElim ≅CompComposablePath hasJElimCompPath

  module _ {l} (C : composablePath X A → Set l) {{_ : {p : composablePath X A} → Fib (C p)}}
           (d : (x : X) → C (composableHrefl x)) where

         JComposablePathAux = hasElimComposablePath C d

         JComposablePath : (p : composablePath X A) → C p
         JComposablePath = Σleft JComposablePathAux
  
         JComposablePathCompute : (x : X) → JComposablePath (composableHrefl x) ≡ d x
         JComposablePathCompute = Σright JComposablePathAux


{-
  module _  {l m} {U : Set l} {V : Set m} {u : U → V} (pseudoCofibu : PseudoCofibration u) where


    --In a first module we show that the type of fillings of a pseudocofibration is fibrant
    
    module _  {m} {Y : Set m} {{_ : Fib Y}} {f : U → Y} where

      PullExp⊤ : PullExp u (Terminal⊤ Y)
      
      PullExp⊤ = record { fun₁ = f ; fun₂ = λ _ → * ; eqPullExp = λ _ → refl }
    
      ≅FibFilling : fibre (< u / Terminal⊤ Y >) PullExp⊤ ≅ Filling u f
      
      ≅FibFilling = record { isoFun = λ { (g , eq) → record { FillingMap = g ;
                                                              FillingCommute = λ x → ap (λ H → H x) (ap PullExp.fun₁ eq) }} ;
                             isIso = record { inv = λ { record { FillingMap = g ;
                                                                 FillingCommute = eq } → g , (≡PullExp (funext (λ a → eq a))
                                                                                                       (funext (λ _ → refl)))} ;
                                              invLeft = λ { record { FillingMap = g ;
                                                                     FillingCommute = _ } → ≡Filling refl} ;
                                              invRight = λ { (g , _) → ≡fibre refl} } }


      instance
        FibTerminal⊤ : Fibration (Terminal⊤ Y)
        
        FibTerminal⊤ {*} = ≅Fib {X = Y} (record { isoFun = λ y → y , refl ;
                                                  isIso = record { inv = λ { (y , _) → y} ;
                                                                   invLeft = λ { (_ , _) → ≡fibre refl} ;
                                                                   invRight = λ _ → refl } })

        FibFilling : Fib (Filling u f)
      
        FibFilling = ≅Fib ≅FibFilling {{pseudoCofibu {p = Terminal⊤ Y}}}


    --We show that PathOp X A has the filling property against any pseudocofibration

    LiftingAux : (ϕ : (p : composablePath X A) → U → firstPoint p ~~> lastPoint p)
                 {ϕrefl : (x : X) (y : U) → ϕ (composableHrefl x) y ≡ hrefl}
                  → (p : composablePath X A) → Filling u (ϕ p)
                                  
    LiftingAux ϕ {ϕrefl} = JComposablePath (λ p → Filling u (ϕ p))
                                           λ x → record { FillingMap = λ _ → hrefl ;
                                                          FillingCommute = λ x' → ≡Sym (ϕrefl x x') }


    LiftingAuxHrefl : (ϕ : (p : composablePath X A) → U → firstPoint p ~~> lastPoint p)
                      {ϕrefl : (x : X) (y : U) → ϕ (composableHrefl x) y ≡ hrefl}
                      (x : X) (y : V) → Filling.FillingMap (LiftingAux ϕ {ϕrefl} (composableHrefl x)) y ≡ hrefl
                                       
    LiftingAuxHrefl ϕ {ϕrefl} x y = ap (λ H → Filling.FillingMap H y)
                                      {x = LiftingAux ϕ {ϕrefl} (composableHrefl x)}
                                      {y = record { FillingMap = λ _ → hrefl ; FillingCommute = λ x' → ≡Sym (ϕrefl x x')}}
                                      (JComposablePathCompute (λ p → Filling u (ϕ p))
                                      (λ x → record { FillingMap = λ _ → hrefl ; FillingCommute = λ x' → ≡Sym (ϕrefl x x')}) x)


    LiftingPseudoCofibPathOp : {v : U → PathOp X A} → Filling u v
                             
    LiftingPseudoCofibPathOp {v} = let ϕ = λ p x → PathOp.fun (v x) p in
                                   let ϕHrefl : (x : X) (y : U) → ϕ (composableHrefl x) y ≡ hrefl
                                       ϕHrefl = λ x y → PathOp.equality (v y) x in
                                   let liftϕ =  LiftingAux ϕ {ϕHrefl} in
                                   record { FillingMap = λ y → record { fun = λ p → Filling.FillingMap (liftϕ p) y ;
                                                                        equality = λ x → LiftingAuxHrefl ϕ {ϕHrefl} x y } ;
                                            FillingCommute = λ x → ≡PathOp (λ p → Filling.FillingCommute (liftϕ p) x) }


  StronglyContractiblePathOp : StronglyContractible (PathOp X A)
  
  StronglyContractiblePathOp u = LiftingPseudoCofibPathOp PseudoCofibBorder




--In this module we build the operad structure on PathOp

module _ {k} {X : Set k} where


  PathOpFun : {A B : Set} → {{_ : FOSet A}} → {{_ : FOSet B}}
              → (f : A → B) → HomFO f → PathOp X A → PathOp X B

  PathOpFun f homf record { fun = ϕ ; equality = eq } =
                   record { fun = λ {p → endpointPath  (ϕ (composablePathFunct f homf p))
                                                      (composablePathFunctFirstPoint f homf p)
                                                      (composablePathFunctLastPoint f homf p)}  ;
                            equality = λ x → ≡Path (λ i → ≡Trans {y = ϕ (composableHrefl x) $ i}
                                                                 (ap (λ H → ϕ H $ i) (composablePathFunctHrefl f homf))
                                                                 (ap (λ p → p $ i) (eq x))) }


  PathOpFunCompute :  {A B : Set} → {{_ : FOSet A}} → {{_ : FOSet B}}
              → {f : A → B} → {homf : HomFO f} → (c : PathOp X A) {p : composablePath X B} {i : I}
              → PathOp.fun (PathOpFun f homf c) p $ i ≡ PathOp.fun c (composablePathFunct f homf p) $ i 

  PathOpFunCompute record { fun = ϕ ; equality = eqϕ } = refl
  

  γPathOp : {A : Set} {B : A → Set} {{_ : FOSet A}} {{_ : {a : A} → FOSet (B a)}}
            → PathOp X A → ((a : A) → PathOp X (B a)) → PathOp X (Σ A B)
  γPathOp {A = A} {B = B} ( record { fun = ϕ ; equality = eqϕ }) d =
                  record { fun = λ {record { point = f ; path = F }
                                    → endpointPath (ϕ (record { point = f o ΣSucc ;
                                                                           path = λ a → endpointPath (PathOp.fun (d a)
                                                                                        (ΣComposablePath a (record { point = f ; path = F })))
                                                                                        (ap f ΣSuccIncMin) refl } ))
                                      (ap (λ a → f a) ΣSuccMin) refl };
                                                        
                              equality = λ x → ≡Trans {y = ϕ (composableHrefl x)}
                                                      (≡Path (λ i → ap (λ H → ϕ H $ i)
                                                      (≡ComposablePath refl
                                                                       (λ a i → ≡Trans {y = PathOp.fun (d a) (composableHrefl x) $ i}
                                                                                       (ap (λ H → PathOp.fun (d a) H $ i) (ΣComposablePathHrefl {B = B}))
                                                                                       (ap (λ H → H $ i) (PathOp.equality (d a) x))))))
                                                      (eqϕ x) }


  γPathOpCompute : {A : Set} {B : A → Set} {{_ : FOSet A}} {{_ : {a : A} → FOSet (B a)}}
                   (c : PathOp X A) (d : (a : A) → PathOp X (B a))
                   {f : Succ (Σ A B) → X} {F : (x : Σ A B) → f (inc₀ x) ~~> f (inc₁ x)} {i : I}
                   → PathOp.fun (γPathOp c d) (record {point = f ; path = F}) $ i
                     ≡ (PathOp.fun c (record { point = f o ΣSucc ; path = λ a → endpointPath (PathOp.fun (d a) (ΣComposablePath a (record { point = f ; path = F })))
                                                                                                        (ap f ΣSuccIncMin) refl }) $ i)

  γPathOpCompute record { fun = ϕ ; equality = eqϕ } d = refl



  idPathOp : PathOp X (Fin (s O))
  idPathOp = record { fun = λ p → composablePath.path p fzero ;
                      equality = λ _ → refl }


  UnitLeftPathOp : {A : Set} ⦃ _ : FOSet A ⦄ (c : PathOp X A) →
                   γPathOp c (λ _ → idPathOp) ≡ PathOpFun (η₂ _) HomFOη₂ c

  UnitLeftPathOp (record { fun = ϕ ; equality = eqϕ }) = ≡PathOp (λ { record { point = f ; path = F }
                                                       → ≡Path (λ i → ap (λ H → ϕ H $ i)
                                                                         (≡ComposablePath refl (λ _ _ → refl)))})


  UnitRightPathOp : {B : Fin (s O) → Set} ⦃ _ : {x : Fin (s O)} → FOSet (B x) ⦄
                    (d : (x : Fin (s O)) → PathOp X (B x)) →
                    γPathOp idPathOp d ≡ PathOpFun (η₁ B) HomFOη₁ (d fzero)

  UnitRightPathOp d = ≡PathOp (λ { record { point = f ; path = F }
                              → ≡Path (λ i → ≡Trans (ap (λ H → PathOp.fun (d fzero) H $ i) (≡ComposablePath refl (λ _ _ → refl)))
                                                    (≡Sym (PathOpFunCompute (d fzero))) ) } )


  NaturalityFiberPathOp : {A : Set} ⦃ _ : FOSet A ⦄ {B₁ B₂ : A → Set} ⦃ _ : {a : A} → FOSet (B₁ a) ⦄ ⦃ _ : {a : A} → FOSet (B₂ a) ⦄
                          (F : {a : A} → B₁ a → B₂ a) (homF : {a : A} → HomFO F)
                          (c : PathOp X A) (d : (a : A) → PathOp X (B₁ a))
                          → PathOpFun (Σfun Id F) (HomFOΣfun HomFOId homF) (γPathOp c d) ≡ γPathOp c (λ a → PathOpFun (F {a}) (homF {a}) (d a))

  NaturalityFiberPathOp F homF record { fun = ϕ ; equality = eqϕ } d = ≡PathOp (λ { record { point = g ; path = G }
                                                                     → ≡Path (λ i → ap (λ H → ϕ H $ i)
                                                                     (≡ComposablePath refl
                                                                     (λ a j → ≡Trans (ap (λ H → PathOp.fun (d a) H $ j)
                                                                                     (≡ComposablePath (ap g (≡Sym (ΣSuccΣFunFibre homF {a = inc₁ a})))
                                                                                                      λ _ _ → refl))
                                                                                     (≡Sym (PathOpFunCompute (d a))))))})



  NaturalityBasePathOp : {A₁ A₂ : Set} ⦃ _ : FOSet A₁ ⦄ ⦃ _ : FOSet A₂ ⦄ {B : A₂ → Set} ⦃ _ : {a₂ : A₂} → FOSet (B a₂) ⦄
                         (f : A₁ → A₂) (homf : HomFO f)
                         (c : PathOp X A₁) (d : (a₂ : A₂) → PathOp X (B a₂))
                         → PathOpFun (Σfun f Id) (HomFOΣfun homf HomFOId) (γPathOp c (d o f)) ≡ γPathOp (PathOpFun f homf c) d

  NaturalityBasePathOp f homf record { fun = ϕ ; equality = eqϕ } d =
                         ≡PathOp (λ { record { point = g ; path = G }
                                 → ≡Path (λ i → ap (λ H → ϕ H $ i)
                                         (≡ComposablePath refl (λ a j → ap (λ H → PathOp.fun (d (f a)) H $ j)
                                                                           (≡ComposablePath (ap g (≡Trans (≡Sym (ΣSuccΣFunBase homf {a = inc₁ a}))
                                                                                                          (≡Sym (ap ΣSucc (inc₁morphism f homf {a})))))
                                                                                            (λ _ _ → refl)))))})





  AssocPathOp : {A : Set} {{Afinite : FOSet A}} {B : A → Set}
                {{Bfinite : {a : A} → FOSet (B a)}} {C : Σ A B → Set}
                {{Cfinite : {x : Σ A B} → FOSet (C x)}} (c : PathOp X A {{Afinite}})
                (d : (a : A) → PathOp X (B a) {{Bfinite}}) (e : (x : Σ A B) → PathOp X (C x) {{Cfinite}}) →
                γPathOp {{FOΣ {{Afinite}} {{Bfinite}}}} {{Cfinite}} (γPathOp {{Afinite}} {{Bfinite}} c d) e ≡
                PathOpFun {{FOΣ {{Afinite}} {{FOΣ {{Bfinite}} {{Cfinite}}}}}} {{FOΣ {{FOΣ {{Afinite}} {{Bfinite}}}} {{Cfinite}}}}
                          (ψ A {{Afinite}} B {{Bfinite}} C {{Cfinite}}) (HomFOψ {{Afinite}} {{Bfinite}} {{Cfinite}})
                          (γPathOp {{Afinite}} {{FOΣ {{Bfinite}} {{Cfinite}}}} c (λ a → γPathOp {{Bfinite}} {{Cfinite}} (d a) (λ b → e (a , b))))

  AssocPathOp record { fun = ϕ ; equality = eqϕ } d e =
              ≡PathOp (λ { record { point = g ; path = G }
                      → ≡Path (λ i → ap (λ H → ϕ H $ i)
                                        (≡ComposablePath refl
                                        (λ a j → ≡Trans (ap (λ H → PathOp.fun (d a) H $ j)
                                                            (≡ComposablePath (ap g (ΣSuccψ (inc₁ a)))
                                                                             (λ b k → ap (λ H → PathOp.fun (e (a , b)) H $ k)
                                                                                         (≡ComposablePath (ap g (≡Trans {y = ΣSucc (ΣSuccInc a (inc₁ b))}
                                                                                                                        (ap ΣSucc ΣSuccIncInc₁)
                                                                                                                        (ΣSuccψInc₁ a (inc₁ b))))
                                                                                                          (λ _ _ → refl)))))
                                                        (≡Sym (γPathOpCompute (d a) (λ b → e (a , b)))))))})



  instance
    OperadPathOp : Operad (PathOp X)
    
    OperadPathOp = record
                     { functor = PathOpFun
                     
                     ; functorId = λ { record { fun = ϕ ; equality = _ }
                                       → ≡PathOp λ p → ≡Path (λ i → ap (λ H → ϕ H $ i) composablePathFunctId)}
                     
                     ; functorComp = λ { {homf = homf} {homg = homg} record { fun = ϕ ; equality = _ }
                                         → ≡PathOp (λ p → ≡Path (λ i → ap (λ H → ϕ H $ i) (composablePathFunctComp homf homg p)))}
                     
                     ; id = idPathOp
                     
                     ; γ = γPathOp
                     
                     ; unitLeft = UnitLeftPathOp 
                     
                     ; unitRight = UnitRightPathOp 
                     
                     ; naturalityFiber = NaturalityFiberPathOp
                     
                     ; naturalityBase = NaturalityBasePathOp
                     
                     ; assoc = AssocPathOp
                     }




--We define the morphisms from the path operad to the endomorphism operads


  PathOpToEnd : (x : X) → Nat (PathOp X) (End (x ~~> x))
  
  PathOpToEnd _ _ ϕ p = PathOp.fun ϕ (loopComposable p)
 

  HomPathOpToEnd : (x : X) → HomOperad (PathOpToEnd x)
  
  HomPathOpToEnd x = record { homNat = λ { {f = f} homf {record { fun = ϕ ; equality = eq }}
                                           → funext (λ a → ≡Path (λ i → (ap (λ H → ϕ H $ i) (loopComposableFunct f homf {a = a}))))} ;
                                           
                              homId = refl ;
                              
                              homγ = λ { {A} {B = B} {c = record { fun = ϕ ; equality = eqϕ }} {d}
                                       → funext (λ p → ≡Path (λ i → ap (λ H → ϕ H $ i)
                                                             (≡ComposablePath refl
                                                             (λ a j → ap (λ H → PathOp.fun (d a) H $ j)
                                                                         (≡ComposablePath refl (λ _ _ → refl)))))) }}





-}
