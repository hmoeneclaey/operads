{-# OPTIONS --no-eta-equality #-}
{-# OPTIONS --allow-unsolved-metas #-}

module LoopSpace where

open import Agda.Primitive
open import Data
open import FibrantUniverse
open import FiniteSet
open import MorphismFiniteSet
open import Operad
open import Cofibration
open import FiniteSet2



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
          
≡PathOpAux {P = record { fun = ϕ ; equality = eqϕ }} {record { fun = ψ ; equality = eqψ }} refl = ap (λ H → record { fun = ϕ ; equality = H }) (funext (λ _ → UIP)) 


≡PathOp : ∀ {k} {X : Set k} {A : Set} {{_ : FOSet A}} {P Q : PathOp X A}
          → ((p : composablePath X A) → PathOp.fun P p ≡ PathOp.fun Q p) → P ≡ Q
          
≡PathOp equalFun = ≡PathOpAux (funext equalFun)



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



--We prove the path operad is strongly contractible


  StronglyContractiblePathOp : {{_ : Fib X}} {A : Set} {{_ : FOSet A}} → StronglyContractible (PathOp X A)
  
  StronglyContractiblePathOp = {!!}



