{-# OPTIONS --rewriting #-}


module Cofibration where

open import Agda.Primitive
open import Data
open import FibrantUniverse



--First we gather auxiliary results about fibrations


proj : ∀ {k l} (X : Set k) (P : X → Set l) → Σ X P → X
proj X P (x , _) = x

≡fibre : ∀ {k l} {X : Set k} {Y : Set l} {f : X → Y} {y : Y} {p q : fibre f y} → fibre.point p ≡ fibre.point q → p ≡ q
≡fibre {p = x₁ , _} {x₂ , _} refl = ap (λ eq → x₁ , eq) UIP

≅fibreProj : ∀ {k l} {X : Set k} {P : X → Set l} {x : X}
             → P x ≅ fibre (proj X P) x
≅fibreProj {x = x} = record { isoFun = λ p → (x , p) , refl ;
                              isIso = record { inv = λ { ((_ , p) , refl) → p} ;
                                               invLeft = λ { ((_ , _) , refl) → refl} ;
                                               invRight = λ _ → refl } }

instance
  projFibration : ∀ {k l} {X : Set k} {P : X → Set l} {{_ : {x : X} → Fib (P x)}} → Fibration (proj X P)
  projFibration = ≅Fib ≅fibreProj




-- We introduce trivial fibrations with fibrant basis

FibrantBasis : ∀ {k l} {X : Set k} {Y : Set l} (p : X → Y) → Set l
FibrantBasis {Y = Y} p = Fib Y

record TrivialFibrationBasis {k l} {X : Set k} {Y : Set l} (p : X → Y) : Set (k ⊔ l) where
  field
    isFib : Fibration p
    isContr : ContrMap p
    isBasis : FibrantBasis p
    




--We introduce some structure on types


module _ {k l m n} {X : Set k} {Y : Set l} {A : Set m} {B : Set n} where

  record PullExp (u : A → B) (p : X → Y) : Set (k ⊔ l ⊔ m ⊔ n) where
    field
      fun₁ : A → X
      fun₂ : B → Y
      eqPullExp : (a : A) → fun₂ (u a) ≡ p (fun₁ a)


  ≡PullExp : {u : A → B} {p : X → Y} {x y : PullExp u p}
             → PullExp.fun₁ x ≡ PullExp.fun₁ y → PullExp.fun₂ x ≡ PullExp.fun₂ y → x ≡ y
             
  ≡PullExp {x = record { fun₁ = f₁ ; fun₂ = f₂ ; eqPullExp = eqf }} {record { fun₁ = g₁ ; fun₂ = g₂ ; eqPullExp = eqg }} refl refl
           = ap (λ eq → record { fun₁ = f₁ ; fun₂ = f₂ ; eqPullExp = eq }) (funext (λ _ → UIP))



  <_/_> : (u : A → B) (p : X → Y) → (B → X) → PullExp u p
  < u / p > f = record { fun₁ = f o u ;
                         fun₂ = p o f ;
                         eqPullExp = λ _ → refl }



postulate
  PushProd : ∀ {k l m n} {A₁ : Set k} {B₁ : Set l} {A₂ : Set m} {B₂ : Set n}
             → (A₁ → B₁) → (A₂ → B₂) → Set (k ⊔ l ⊔ m ⊔ n)



module _ {k l m n} {A₁ : Set k} {B₁ : Set l} {A₂ : Set m} {B₂ : Set n}
         {u : A₁ → B₁} {v : A₂ → B₂} where

       postulate
         inj₁ : A₁ → B₂ → PushProd u v
         inj₂ : B₁ → A₂ → PushProd u v
         eqPushProd : (a₁ : A₁) (a₂ : A₂) → inj₁ a₁ (v a₂) ≡ inj₂ (u a₁) a₂

       module _ {o} {P : PushProd u v → Set o}
                (tinj₁ : (a : A₁) → (b : B₂) → P (inj₁ a b))
                (tinj₂ : (b : B₁) → (a : A₂) → P (inj₂ b a))
                (_ : (a₁ : A₁) → (a₂ : A₂) → transport P (eqPushProd a₁ a₂) (tinj₁ a₁ (v a₂)) ≡ tinj₂ (u a₁) a₂)where

              postulate
                PushProdElim : (x  : PushProd u v) → P x
                
                PushProdCompute₁ :  (a : A₁) → (b : B₂) → PushProdElim (inj₁ a b) ↦ tinj₁ a b
                {-# REWRITE PushProdCompute₁ #-}
                
                PushProdCompute₂ :  (b : B₁) → (a : A₂) → PushProdElim (inj₂ b a) ↦ tinj₂ b a
                {-# REWRITE PushProdCompute₂ #-}



       PushProdRec : ∀ {o} {C : Set o}
                     (tinj₁ : (a : A₁) → (b : B₂) → C)
                     (tinj₂ : (b : B₁) → (a : A₂) → C)
                     → ((a₁ : A₁) → (a₂ : A₂) → (tinj₁ a₁ (v a₂)) ≡ tinj₂ (u a₁) a₂)
                     → PushProd u v → C
                     
       PushProdRec tinj₁ tinj₂ eq = PushProdElim tinj₁ tinj₂ (λ a₁ a₂ → ≡Trans transportConst (eq a₁ a₂))



_□_ : ∀ {k l m n} {A₁ : Set k} {B₁ : Set l} {A₂ : Set m} {B₂ : Set n}
      (u : A₁ → B₁) (v : A₂ → B₂) → PushProd u v → B₁ ∧ B₂

u □ v = PushProdRec (λ a b → (u a) , b)
                    (λ b a → b , (v a))
                    λ _ _ → refl





-- We define isomorphisms of map, and show that several notions are invariant by them


record _≅Map_ {k l m n} {A : Set k} {B : Set l} {X : Set m} {Y : Set n}
              (u : A → B) (p : X → Y) : Set (k ⊔ l ⊔ m ⊔ n) where
  field
    funTop : A → X
    funBot : B → Y
    isoTop : iso funTop
    isoBot : iso funBot
    commute : (a : A) → funBot (u a) ≡ p (funTop a)





-- We show fibre of isomorphic maps are isomorphic

module _  {k l m n} {A : Set k} {B : Set l} {X : Set m} {Y : Set n}
          {u : A → B} {p : X → Y} where

       ≅MapFibre : (uisop : u ≅Map p) → {y : Y} → fibre u (iso.inv (_≅Map_.isoBot uisop) y) ≅ fibre p y 
       ≅MapFibre record { funTop = f ;
                          funBot = g ;
                          isoTop = record { inv = invf ; invLeft = invLeftf ; invRight = invRightf } ;
                          isoBot = record { inv = invg ; invLeft = invLeftg ; invRight = invRightg } ;
                          commute = commute }

                 = record { isoFun = λ { (a , eqa) → f a , ≡Trans {y = g (u a)}
                                                                  (≡Sym (commute _))
                                                                  (≡Trans {y = g (invg _)} (ap g eqa) (≡Sym (invLeftg _)))} ;
                            isIso = record { inv = λ { (x , eqx) → (invf x) , ≡Trans {y = invg (g (u (invf x)))}
                                                                                     (invRightg _)
                                                                                     (≡Trans {y = invg (p (f (invf x)))}
                                                                                             (ap invg (commute _))
                                                                                             (ap invg (≡Trans {y = p x}
                                                                                                      (ap p (≡Sym (invLeftf _)))
                                                                                                      eqx)))} ;
                                             invLeft = λ { (x , eqx) → ≡fibre (invLeftf _)} ;
                                             invRight = λ { (a , eqa) → ≡fibre (invRightf _) } } }




--Homotopical properties are invariant by isomorpism of maps

module _  {k l m n} {A : Set k} {B : Set l} {X : Set m} {Y : Set n}
          {u : A → B} {p : X → Y} (uisop : u ≅Map p) where
          
       ≅MapFibration : {{_ : Fibration u}} → Fibration p
       ≅MapFibration = ≅Fib (≅MapFibre uisop)

       ≅MapContractible : ContrMap u → ContrMap p
       ≅MapContractible contru = ≅Contr (≅MapFibre uisop) contru

       ≅MapFibrantBasis : {{_ : FibrantBasis u}} → FibrantBasis p
       ≅MapFibrantBasis = ≅Fib {X = B} (record { isoFun = _≅Map_.funBot uisop ; isIso = _≅Map_.isoBot uisop })

       ≅MapTrivialFibrationBasis : TrivialFibrationBasis u → TrivialFibrationBasis p
       ≅MapTrivialFibrationBasis record { isFib = fibu ; isContr = contru ; isBasis = baseu }
                               = record { isFib = ≅MapFibration {{fibu}} ;
                                          isContr = ≅MapContractible contru ;
                                          isBasis = ≅MapFibrantBasis {{baseu}} }






--We define the unique map from ⊥ to ⊤, and compute < ⊥ → ⊤ / f> iso to f

empty : ⊥ → ⊤ {lzero}
empty ()

≅empty : ∀ {k l} {X : Set k} {Y : Set l} {p : X → Y} → p ≅Map < empty / p >
≅empty = record
           { funTop = λ x _ → x ;
             funBot = λ y → record { fun₁ = λ () ;
                                     fun₂ = λ _ → y ;
                                     eqPullExp = λ () } ;
             isoTop = record { inv = λ f → f * ;
                               invLeft = λ _ → refl ;
                               invRight = λ _ → refl } ;
             isoBot = record { inv = λ { record { fun₁ = _ ;
                                                  fun₂ = f ;
                                                  eqPullExp = _ } → f *} ;
                               invLeft = λ { record { fun₁ = _ ;
                                                      fun₂ = f ;
                                                      eqPullExp = _} → ≡PullExp (funext (λ ())) refl} ;
                               invRight = λ a → refl } ;
             commute = λ a → ≡PullExp (funext (λ ())) refl }





--We define the border of the interval

data δI : Set where
  δe₀ : δI
  δe₁ : δI

Endpoint : δI → I
Endpoint δe₀ = e₀
Endpoint δe₁ = e₁



--We define a map which will be isomorphic to <Endpoint / f>

module _ {k l} {X : Set k} {Y : Set l} (f : X → Y) where

  record baseEndpoint : Set (k ⊔ l) where
    field
      path : I → Y
      de₀ : fibre f (path e₀)
      de₁ : fibre f (path e₁)

  mapToBaseEndpoint : (I → X) → baseEndpoint
  mapToBaseEndpoint p = record { path = f o p ;
                                 de₀ = (p e₀) , refl ;
                                 de₁ = (p e₁) , refl }
                                 


module _ {k l} {X : Set k} {Y : Set l} {f : X → Y} where


  ≡BaseEndpoint : {x y : baseEndpoint f}
                  → (baseEndpoint.path x) ≡ (baseEndpoint.path y)
                  → fibre.point (baseEndpoint.de₀ x) ≡ fibre.point (baseEndpoint.de₀ y)
                  → fibre.point (baseEndpoint.de₁ x) ≡ fibre.point (baseEndpoint.de₁ y)
                  → x ≡ y

  ≡BaseEndpoint {record { path = p₁ ; de₀ = x₁ , eqx₁ ; de₁ = x₂ , eqx₂ }}
                   {record { path = p₂ ; de₀ = x₃ , eqx₃ ; de₁ = y' , eqy' }} refl refl refl
                   = ap₂
                       (λ eq₁ eq₂ →
                          record { path = p₁ ; de₀ = x₁ , eq₁ ; de₁ = x₂ , eq₂ })
                       UIP UIP


  --We show the desired isomorphism of map

  ≅MapEndpoints : (mapToBaseEndpoint f) ≅Map < Endpoint / f >

  ≅MapEndpoints = record
                    { funTop = Id ;
                      funBot =  λ { record { path = p ;
                                             de₀ = (x , eqx) ;
                                             de₁ = (y , eqy) }
                                  → record { fun₁ = λ { δe₀ → x ; δe₁ → y} ;
                                             fun₂ = p ;
                                             eqPullExp = λ { δe₀ → ≡Sym eqx ; δe₁ → ≡Sym eqy} }} ;
                      isoTop = isoId ;
                      isoBot = record { inv = λ { record { fun₁ = u ;
                                                           fun₂ = v ;
                                                           eqPullExp = equv }
                                                → record { path = v ;
                                                           de₀ = (u δe₀) , (≡Sym (equv _)) ;
                                                           de₁ = (u δe₁) , (≡Sym (equv _)) }} ;
                                        invRight = λ { record { path = p ;
                                                               de₀ = (x , eqx) ;
                                                               de₁ = (y , eqy) } → ≡BaseEndpoint refl refl refl } ;
                                        invLeft = λ { record { fun₁ = u ;
                                                               fun₂ = v ;
                                                               eqPullExp = equv }
                                                            → ≡PullExp (funext (λ { δe₀ → refl ;
                                                                                    δe₁ → refl})) refl} } ;
                      commute = λ p → ≡PullExp (funext (λ { δe₀ → refl ; δe₁ → refl})) refl }



  --We compute the fibre of mapToBaseEndpoint

  fibreBaseEndpoint : (x : baseEndpoint f) → Set (k ⊔ l)

  fibreBaseEndpoint record { path = p ; de₀ = x ; de₁ = y } = dPath (fibre f o p) x y
  

  ≅fibreBaseInv : {x : baseEndpoint f} → fibre (mapToBaseEndpoint f) x → fibreBaseEndpoint x
  
  ≅fibreBaseInv {record { path = p ; de₀ = x ; de₁ = y }} (a , refl) = [ (λ i → (a i) , refl) , refl , refl ]


  ≅fibreBaseInvAux : {x : baseEndpoint f}
                     (a : fibre (mapToBaseEndpoint f) x)
                     {i : I} → fibre.point a i ≡ fibre.point (≅fibreBaseInv a $ i)

  ≅fibreBaseInvAux {record { path = p ; de₀ = x ; de₁ = y }} (a , refl) = refl


  ≅fibreBaseEndpoint : {x : baseEndpoint f}
                    → fibreBaseEndpoint x ≅ fibre (mapToBaseEndpoint f) x
                    
  ≅fibreBaseEndpoint {record { path = p ;
                               de₀ = x ;
                               de₁ = y }}
                   = record { isoFun = λ { [ p , eq₀ , eq₁ ] → (λ i → fibre.point (p i)) ,
                                                                ≡BaseEndpoint (funext (λ i → fibre.equal (p i)))
                                                                              (ap fibre.point eq₀)
                                                                              (ap fibre.point eq₁)} ;
                              isIso = record { inv = ≅fibreBaseInv ;
                                               invLeft = λ { (a , refl) → ≡fibre refl} ;
                                               invRight = λ { [ q , refl , refl ] → (≡dPath (λ i →
                                                                                            ≡fibre (≅fibreBaseInvAux ( fibre.point o q ,
                                                                                                    ≡BaseEndpoint (funext (fibre.equal o q))
                                                                                                                  refl refl))))}}}


  --We show that mapToBaseEndpoint has the property we expect

  instance
    FibMapToBaseEndpoint : {{_ : Fibration f}} → Fibration (mapToBaseEndpoint f)
    FibMapToBaseEndpoint = ≅Fib ≅fibreBaseEndpoint





--We define pseudo-cofibrations


PseudoCofibration : ∀ {m} {n} {A : Set m} {B : Set n} (u : A → B) → Setω

PseudoCofibration u = ∀ {k} {l} {X : Set k} → {Y : Set l} → {p : X → Y}
                      → {{_ : Fibration p}} → Fibration (< u / p >)


PseudoCofibEmpty : PseudoCofibration empty

PseudoCofibEmpty = ≅MapFibration ≅empty



PseudoCofibEndpoint : PseudoCofibration Endpoint

PseudoCofibEndpoint = ≅MapFibration ≅MapEndpoints {{≅Fib ≅fibreBaseEndpoint}}



--We define cofibrations

Cofibration :  ∀ {m} {n} {A : Set m} {B : Set n} (u : A → B) → Setω

Cofibration u = ∀ {k} {l} {X : Set k} → {Y : Set l} → (p : X → Y)
                → TrivialFibrationBasis p → TrivialFibrationBasis (< u / p >)
