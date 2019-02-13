{-# OPTIONS --rewriting #-}


module Cofibration where

open import Agda.Primitive
open import Data
open import FibrantUniverse



--First we gather auxiliary results about the homotopical structure.


--proj : ∀ {k l} (X : Set k) (P : X → Set l) → Σ X P → X
--proj X P (x , _) = x

≡fibre : ∀ {k l} {X : Set k} {Y : Set l} {f : X → Y} {y : Y} {p q : fibre f y} → fibre.point p ≡ fibre.point q → p ≡ q
≡fibre {p = x₁ , _} {x₂ , _} refl = ap (λ eq → x₁ , eq) UIP



{-
≅fibreProj : ∀ {k l} {X : Set k} {P : X → Set l} {x : X}
             → P x ≅ fibre (proj X P) x
≅fibreProj {x = x} = record { isoFun = λ p → (x , p) , refl ;
                              isIso = record { inv = λ { ((_ , p) , refl) → p} ;
                                               invLeft = λ { ((_ , _) , refl) → refl} ;
                                               invRight = λ _ → refl } }

instance
  projFibration : ∀ {k l} {X : Set k} {P : X → Set l} {{_ : {x : X} → Fib (P x)}} → Fibration (proj X P)
  projFibration = ≅Fib ≅fibreProj
-}


≅I→ : ∀ {k} {X : Set k} → (Σ X (λ x → Σ X (λ y → x ~~> y))) ≅ (I → X)
≅I→ = record { isoFun = λ { (x , (y , p)) i → p $ i} ;
               isIso = record { inv = λ p → (p e₀) , ((p e₁) , [ p , refl , refl ]) ;
                                invLeft = λ _ → refl ;
                                invRight = λ { (x , (y , [ p , refl , refl ])) → refl} } }

instance
  ICofib : ∀ {k} {X : Set k} {{_ : Fib X}} → Fib (I → X)
  ICofib = ≅Fib ≅I→




--Being contractible is fibrant


≅ContrΣ : ∀ {k} {X : Set k} → Σ X (λ x → (y : X) → x ~~> y) ≅ Contr X
≅ContrΣ = record { isoFun = λ { (x , p) → record { center = x ; path = p }} ;
                   isIso = record { inv = λ { record { center = x ; path = p } → (x , p)} ;
                                    invLeft = λ { record { center = _ ; path = _ } → refl} ;
                                    invRight = λ { (_ , _) → refl} } }


instance
  FibContr : ∀ {k} {X : Set k} {{_ : Fib X}} → Fib (Contr X)
  FibContr = ≅Fib ≅ContrΣ



--We show easy lemmas about contractible types

 
≃Contr : ∀ {k l} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}}
         → {f : X → Y} → Equiv f → Contr Y → Contr X

≃Contr {f = f} record { hinv₁ = _ ;
                        hinvLeft = _ ;
                        hinv₂ = g₂ ;
                        hinvRight = hinvRight }
               record { center = x ;
                        path = path }
             = record { center = g₂ x ;
                        path = λ y → hap g₂ (path (f y)) # inv (hinvRight y) }


Contr⊤Path : ∀ {k} {x y : ⊤ {k}} → Contr (x ~~> y)

Contr⊤Path = record { center = hrefl ;
                      path = λ y → cstPath (≡Path (λ i → refl)) }



module _ {k} {X : Set k} (contrX : Contr X) {{_ : Fib X}} where


  EquivContr⊤ : Equiv (λ (_ : X) → * {lzero})
  
  EquivContr⊤ = record { hinv₁ = λ _ → Contr.center contrX ;
                         hinvLeft = λ _ → hrefl ;
                         hinv₂ = λ _ → Contr.center contrX ;
                         hinvRight = λ x → inv (Contr.path contrX x) }


  ContrPath : {x y : X} → Contr (x ~~> y)
  
  ContrPath = ≃Contr (EquivHap EquivContr⊤) Contr⊤Path


ContrdPath : ∀ {k l} {Y : Set k} {{_ : Fib Y}}
             {P : Y → Set l} {{_ : {y : Y} → Fib (P y)}}
             → ({y : Y} → Contr (P y)) → (p : I → Y)
             → (x : P (p e₀)) → (y : P (p e₁)) → Contr (dPath (P o p) x y)
             
ContrdPath {P = P} contrP = J _ λ y p₁ p₂ → ContrPath contrP






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
                (_ : (a₁ : A₁) → (a₂ : A₂) → transport P (eqPushProd a₁ a₂) (tinj₁ a₁ (v a₂)) ≡ tinj₂ (u a₁) a₂) where

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

Empty : ⊥ → ⊤ {lzero}
Empty ()

≅Empty : ∀ {k l} {X : Set k} {Y : Set l} {p : X → Y} → p ≅Map < Empty / p >
≅Empty = record
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
                                               invRight = λ { [ q , refl , refl ]
                                                              → (≡dPath (λ i → ≡fibre (≅fibreBaseInvAux ( fibre.point o q ,
                                                                                       ≡BaseEndpoint (funext (fibre.equal o q))
                                                                                                     refl refl))))}}}


  --We show that mapToBaseEndpoint has the property we expect

  instance
    FibMapToBaseEndpoint : {{_ : Fibration f}} → Fibration (mapToBaseEndpoint f)
    FibMapToBaseEndpoint = ≅Fib ≅fibreBaseEndpoint

  
  ≅BaseEndpoint : Σ (I → Y) (λ p → fibre f (p e₀) ∧ fibre f (p e₁)) ≅ baseEndpoint f
  
  ≅BaseEndpoint = record { isoFun = λ { (p , (x , y)) → record { path = p ;
                                                                 de₀ = x ;
                                                                 de₁ = y }} ;
                           isIso = record { inv = λ { record { path = p ;
                                                               de₀ = x ;
                                                               de₁ = y } → (p , (x , y))} ;
                                            invLeft = λ { record { path = _ ; de₀ = _ ; de₁ = _ } → refl} ;
                                            invRight = λ { (_ , (_ , _)) → refl} } }


  FibBaseEndpoint : {{_ : Fibration f}} → {{_ : Fib Y}} → Fib (baseEndpoint f)

  FibBaseEndpoint = ≅Fib ≅BaseEndpoint


  ContrMapToBaseEndpoint : {{_ : Fibration f}} → {{_ : Fib Y}} → ContrMap f → {y : baseEndpoint f} → Contr (fibreBaseEndpoint y)

  ContrMapToBaseEndpoint contrf {record { path = p ; de₀ = x ; de₁ = y }} = ContrdPath {Y = Y} {P = fibre f} contrf p x y


  TrivFibMapToBaseEndpoint : TrivialFibrationBasis f → TrivialFibrationBasis (mapToBaseEndpoint f)
  
  TrivFibMapToBaseEndpoint record { isFib = fibf ;
                                    isContr = contrf ;
                                    isBasis = fibY }
                         = record { isFib = FibMapToBaseEndpoint {{fibf}} ;
                                    isContr = ≅Contr ≅fibreBaseEndpoint (ContrMapToBaseEndpoint {{fibf}} {{fibY}} contrf) ; 
                                    isBasis = FibBaseEndpoint {{fibf}} {{fibY}} }











--We define the iteration of □, and then the inclusion of the border in any cube


Prod : ∀ {k} (X : Set k) → ℕ → Set k
Prod X O = ⊤
Prod X (s n) = Prod X n ∧ X

--We give a mutual inductive definition of the iterated Pushout-Product.
--Note we give it only for Set, although a polymorphic version could be stated

module _ {X Y : Set} (f : X → Y) where

  IteratedPushProd : ℕ → Set
  Iterated□ : (k : ℕ) → IteratedPushProd k → Prod Y k

  IteratedPushProd O = ⊥
  IteratedPushProd (s n) = PushProd (Iterated□ n) f
  
  Iterated□ O = Empty
  Iterated□ (s n) = (Iterated□ n) □ f

borderI : ℕ → Set
borderI k = IteratedPushProd Endpoint k

border : (k : ℕ) → borderI k → Prod I k
border k = Iterated□ Endpoint k



--Show the main property of _□_ and <_/_>

module _  {k l m n p q} {X : Set k} {Y : Set l} {A : Set m} {B : Set n} {C : Set p} {D : Set q}
          {u : A → B} {v : C → D} {p : X → Y} where

       ≅Map□ : < (u □ v) / p > ≅Map < u / < v / p > >

       ≅Map□ = record
                 { funTop = λ f x y → f (x , y) ;
                 
                   funBot = λ { record { fun₁ = f ;
                                         fun₂ = g ;
                                         eqPullExp = eq }
                              → record { fun₁ = λ a d → f (inj₁ a d) ;
                                         fun₂ = λ b → record { fun₁ = λ c → f (inj₂ b c) ;
                                                               fun₂ = λ d → g (b , d) ;
                                                               eqPullExp = λ c → (eq _) } ;
                                         eqPullExp = λ a → ≡PullExp (funext (λ c → ap f (≡Sym (eqPushProd a c))))
                                                                    (funext (λ d → eq _)) }} ;
                   
                   isoTop = record { inv = λ {f (x , y) → f x y} ;
                                     invLeft = λ f → refl ;
                                     invRight = λ f → funext (λ {(x , y) → refl}) } ;
                                     
                   isoBot = record { inv = λ { record { fun₁ = f ;
                                                        fun₂ = g ;
                                                        eqPullExp = eq }
                                             → record { fun₁ = PushProdRec f
                                                                           (λ b c → PullExp.fun₁ (g b) c)
                                                                           λ a c → ≡Sym (ap (λ F → PullExp.fun₁ F c) (eq a)) ; 
                                                        fun₂ = λ {(b , d) → PullExp.fun₂ (g b) d} ; 
                                                        eqPullExp = PushProdElim (λ a b → ap (λ F → PullExp.fun₂ F b) (eq a))
                                                                                 (λ b c → PullExp.eqPullExp (g b) _)
                                                                                 (λ _ _ → UIP) }} ;
                                     invLeft = λ { record { fun₁ = f ;
                                                            fun₂ = g ;
                                                            eqPullExp = eq }
                                                 → ≡PullExp refl
                                                            refl} ;
                                     invRight = λ { record { fun₁ = f ;
                                                             fun₂ = g ;
                                                             eqPullExp = eq }
                                                  → ≡PullExp (funext (PushProdElim (λ _ _ → refl)
                                                                                   (λ _ _ → refl)
                                                                                   λ _ _ → UIP))
                                                             (funext (λ { (_ , _) → refl}))} } ;
                   
                   commute = λ f → ≡PullExp refl refl }



≅MapSym : ∀ {k l m n} {A : Set k} {B : Set l} {C : Set m} {D : Set n}
          {u : A → B} {v : C → D} → u ≅Map v → v ≅Map u

≅MapSym {u = u} {v}
        record { funTop = f ;
                 funBot = g ;
                 isoTop = isof ;
                 isoBot = isog ;
                 commute = commute }
      = record { funTop = iso.inv isof ;
                 funBot = iso.inv isog ;
                 isoTop = isoInv isof ;
                 isoBot = isoInv isog ;
                 commute = λ a → let invg = iso.inv isog in
                                 let invf = iso.inv isof in
                                  ≡Trans {y = invg (g (u (invf a)))}
                                         (ap invg (≡Trans {y = v (f (invf a))}
                                                          (ap v (iso.invLeft isof _))
                                                          (≡Sym (commute _))))
                                         (≡Sym (iso.invRight isog _)) }



--We define pseudo-cofibrations, and prove that δ(I k) → I k is an example


PseudoCofibration : ∀ {m} {n} {A : Set m} {B : Set n} (u : A → B) → Setω

PseudoCofibration u = ∀ {k} {l} {X : Set k} → {Y : Set l} → {p : X → Y}
                      → {{_ : Fibration p}} → Fibration (< u / p >)


PseudoCofibEmpty : PseudoCofibration Empty

PseudoCofibEmpty = ≅MapFibration ≅Empty


PseudoCofibEndpoint : PseudoCofibration Endpoint

PseudoCofibEndpoint = ≅MapFibration ≅MapEndpoints


PseudoCofib□ : ∀ {k l m n} {A : Set k} {B : Set l} {C : Set m} {D : Set n}
               {u : A → B} {v : C → D}
               → PseudoCofibration u → PseudoCofibration v → PseudoCofibration (u □ v)

PseudoCofib□ cofibu cofibv = ≅MapFibration (≅MapSym ≅Map□) {{cofibu {{cofibv}}}}


PseudoCofibIterated□ : {A B : Set} {u : A → B} {k : ℕ} → PseudoCofibration u → PseudoCofibration (Iterated□ u k)

PseudoCofibIterated□ {k = O} cofibu = PseudoCofibEmpty

PseudoCofibIterated□ {k = s k} cofibu = PseudoCofib□ (PseudoCofibIterated□ cofibu) cofibu


PseudoCofibBorder : {k : ℕ} → PseudoCofibration (border k)

PseudoCofibBorder = PseudoCofibIterated□ PseudoCofibEndpoint



--We define cofibrations, and prove that δ(I k) → I k is an example


Cofibration :  ∀ {m} {n} {A : Set m} {B : Set n} (u : A → B) → Setω

Cofibration u = ∀ {k} {l} {X : Set k} → {Y : Set l} → {p : X → Y}
                → TrivialFibrationBasis p → TrivialFibrationBasis (< u / p >)


CofibEmpty : Cofibration Empty

CofibEmpty tfibbp = ≅MapTrivialFibrationBasis ≅Empty tfibbp


CofibEndpoint : Cofibration Endpoint

CofibEndpoint tfibbp = ≅MapTrivialFibrationBasis ≅MapEndpoints (TrivFibMapToBaseEndpoint tfibbp)


Cofib□ : ∀ {k l m n} {A : Set k} {B : Set l} {C : Set m} {D : Set n}
        {u : A → B} {v : C → D}
        → Cofibration u → Cofibration v → Cofibration (u □ v)

Cofib□ cofibu cofibv tfibp = ≅MapTrivialFibrationBasis (≅MapSym ≅Map□) (cofibu (cofibv tfibp))


CofibIterated□ : {A B : Set} {u : A → B} {k : ℕ} → Cofibration u → Cofibration (Iterated□ u k)

CofibIterated□ {k = O} cofibu = CofibEmpty

CofibIterated□ {k = s k} cofibu = Cofib□ (CofibIterated□ cofibu) cofibu


CofibBorder : {k : ℕ} → Cofibration (border k)

CofibBorder = CofibIterated□ CofibEndpoint

