{-# OPTIONS --rewriting #-}


--This module will contains the fibrant universes and their homotopical structure. 

module FibrantUniverses where


open import Data
open import Agda.Primitive


postulate _↦_ : ∀ {i} {A : Set i} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}




--Here we write every postulate for the fibrant universes
--Q : Fib Set k → Set is okay ?

postulate
  I : Set
  e₀ e₁ : I
  _⊓_ : I → I → I
  
infixl 32 _⊓_

postulate
  ⊓left₀ : {i : I} → e₀ ⊓ i ≡ e₀
  ⊓right₀ : {i : I} → i ⊓ e₀ ≡ e₀
  ⊓left₁ : {i : I} → e₁ ⊓ i ≡ i 
  ⊓right₁ : {i : I} → i ⊓ e₁ ≡ i


record dPath {k} (P : I → Set k) (x : P e₀) (y : P e₁) : Set k where
  constructor [_,_,_]
  field
    dpath : (i : I) → P i
    deq₀ : dpath e₀ ≡ x
    deq₁ : dpath e₁ ≡ y


postulate
  Fib : ∀ {k} → Set k → Set k

  instance
    ⊤Fib : ∀ {k} → Fib (⊤ {k})
  
    ΠFib : ∀ {k l} {A : Set k} {{_ : Fib A}} {B : A → Set l} {{_ : {a : A} → Fib (B a)}}
           → Fib ((a : A) → B a)
         
    ΣFib : ∀ {k l} {A : Set k} {{_ : Fib A}} {B : A → Set l} {{fibB : {a : A} → Fib (B a)}}
           → Fib (Σ A B)
         
    IFib : ∀ {k} {P : I → Set k} {{_ : (i : I) → Fib (P i)}} {x : P e₀} {y : P e₁}
           → Fib (dPath P x y)

  ≅Fib : ∀ {k l} {X : Set k} {Y : Set l} → X ≅ Y → {{_ : Fib X}} → Fib Y


module _ {k l} {X : Set k} {{_ : Fib X}} 
  (C : (I → X) → Set l) {{_ : (p : I → X) → Fib (C p)}} 
  (d : (x : X) → C (λ i → x)) where
  postulate
    J : (p : I → X) → C p
    Jcompute : (x : X) → J (λ i → x) ↦ d x
    {-# REWRITE Jcompute #-}





--Now we give definition of paths

Path : ∀ {k} (X : Set k) (x y : X) → Set k
Path X x y = dPath (λ _ → X) x y

_$_ : ∀ {k} {P : I → Set k} {x : P e₀} {y : P e₁} → dPath P x y → (i : I) → P i
p $ i  = (dPath.dpath p) i

infix 35 _$_

eqe₀ : ∀ {k} {P : I → Set k} {x : P e₀} {y : P e₁} (p : dPath P x y) → p $ e₀ ≡ x
eqe₀ p = dPath.deq₀ p

eqe₁ : ∀ {k} {P : I → Set k} {x : P e₀} {y : P e₁} (p : dPath P x y) → p $ e₁ ≡ y
eqe₁ p = dPath.deq₁ p





--Basic properties of paths

module _ {k} {X : Set k} where

  hrefl : {x : X} → Path X x x
  hrefl {x} = [ (λ i → x) , refl , refl ]

  cstPath : {x y : X} → x ≡ y → Path X x y
  cstPath {x} = λ p → [ (λ i → x) , refl , p ]

  endpointPath : {x₁ x₂ y₁ y₂ : X} → Path X x₁ y₁ → x₁ ≡ x₂ → y₁ ≡ y₂ → Path X x₂ y₂
  endpointPath p eq₁ eq₂ = [ (λ i → p $ i) ,
                      ≡Trans (eqe₀ p) eq₁ ,
                      ≡Trans (eqe₁ p) eq₂ ]

  ≡PathAux : {x y : X} {p q : I → X} {eqp₀ : p e₀ ≡ x} {eqp₁ : p e₁ ≡ y} {eqq₀ : q e₀ ≡ x} {eqq₁ : q e₁ ≡ y}
             → p ≡ q → [ p , eqp₀ , eqp₁ ] ≡ [ q , eqq₀ , eqq₁ ]
  ≡PathAux {p = p} {eqp₀ = eqp₀} {eqq₁ = eqq₁} refl = ≡Trans {y = [ p , eqp₀ , eqq₁ ]}
                                                             (ap (λ e → [ _ , _ , e ]) UIP)
                                                             (ap (λ e → [ _ , e , _ ]) UIP) 

  ≡Path : {x y : X} → {p q : Path X x y} → ((i : I) → p $ i ≡ q $ i) → p ≡ q
  ≡Path {p = [ p , eqp₀ , eqp₁ ]} {[ q , eqq₀ , eqq₁ ]} hyp = ≡PathAux (funext hyp)


module _ {k} {X : Set k} {{_ : Fib X}} where

  inv : {x y : X} → Path X x y → Path X y x
  inv [ p , refl , refl ] = J (λ p → Path X (p e₁) (p e₀)) (λ _ → hrefl) p

  PathTrans : {x y z : X} → Path X x y → Path X y z → Path X x z
  PathTrans {z = z} [ p , refl , refl ] = J (λ p₁ → (Path X (p₁ e₁) z → Path X (p₁ e₀) z)) (λ x q → q) p

  _#_ : {x y z : X} → Path X x y → Path X y z → Path X x z
  p # q = PathTrans p q



module _ {k l} {X : Set k} {Y : Set l} where

  hap : (f : X → Y) {x₁ x₂ : X} → Path X x₁ x₂ → Path Y (f x₁) (f x₂) 
  hap f p = [ (λ i → f (p $ i)) ,
              ap f (eqe₀ p) ,
              ap f (eqe₁ p) ]

  hfunext : {f g : X → Y} → ((x : X) → Path Y (f x) (g x)) → Path (X → Y) f g
  hfunext Hyp = [ (λ i x → (Hyp x) $ i) ,
                  funext (λ x → eqe₀ (Hyp x)) ,
                  funext (λ x → eqe₁ (Hyp x)) ]



--Define contractibility

record Contr {k} (X : Set k) : Set k where
  field
    center : X
    path : (y : X) → Path X center y




--Properties of maps

module _ {k l} {X : Set k} {Y : Set l} (f : X → Y) where

{-
  fibre : Y → Set (k ⊔ l)
  fibre y = Σ X (λ x → f x ≡ y)
-}

  record fibre (y : Y) : Set (k ⊔ l) where
    constructor _,_
    field
      point : X
      equal : f point ≡ y

  --We do not use record because we want hfibre to be fibrant using ΣFib
  hfibre : (y : Y) → Set (k ⊔ l)
  hfibre y = Σ X (λ x → Path Y (f x) y)

  Fibration : Set (k ⊔ l)
  Fibration = {y : Y} → Fib (fibre y)

  ContrMap : Set (k ⊔ l)
  ContrMap = {y : Y} → Contr (fibre y)

  record TrivialFibration : Set (k ⊔ l) where
    field
      isFib : Fibration
      isContr : ContrMap

  record Equiv : Set (k ⊔ l) where
    field
      hinv₁ : Y → X
      hinvLeft : (y : Y) → Path Y y (f (hinv₁ y))
      hinv₂ : Y → X
      hinvRight : (x : X) → Path X x (hinv₂ (f x))













--Results about equivalences



--We will probably need something more, like Equiv g → Equiv (hap g)

hapinv : ∀ {k l} {X : Set k} {{_ : Fib X}} {Y : Set l}
         {f : X → Y} {x y : X}
         → Equiv f → Path Y (f x) (f y) → Path X x y

hapinv {f = f} record { hinv₁ = _ ; hinvLeft = _ ; hinv₂ = g₂ ; hinvRight = hinvg₂ } p 
             = hinvg₂ _ # (hap g₂ p # inv (hinvg₂ _))  



module _ {k l m} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}} {Z : Set m} {{_ : Fib Z}} where
  
  EquivComp : {f : X → Y} {g : Y → Z} → Equiv f → Equiv g → Equiv (g o f)
  EquivComp {f}{g}
            record { hinv₁ = f₁ ;
                     hinvLeft = hinvf₁ ;
                     hinv₂ = f₂ ;
                     hinvRight = hinvf₂ }
            record { hinv₁ = g₁ ;
                     hinvLeft = hinvg₁ ;
                     hinv₂ = g₂ ;
                     hinvRight = hinvg₂ }
          = record { hinv₁ = f₁ o g₁ ;
                     hinvLeft = λ z → hinvg₁ _ # hap g (hinvf₁ _) ;
                     hinv₂ = f₂ o g₂ ;
                     hinvRight = λ x → hinvf₂ _ # hap f₂ (hinvg₂ _) }

  
  EquivTwoThreeRight : {f : X → Y} {g : Y → Z} → Equiv g → Equiv (g o f) → Equiv f 
  EquivTwoThreeRight {g = g}
                     equivg
                     record { hinv₁ = gf₁ ;
                              hinvLeft = hinvgf₁ ;
                              hinv₂ = gf₂ ;
                              hinvRight = hinvgf₂ }
                   = record { hinv₁ = gf₁ o g ;
                              hinvLeft = λ y → hapinv equivg (hinvgf₁ _) ;
                              hinv₂ = gf₂ o g ;
                              hinvRight = λ x → hinvgf₂ _ }


module _ {k l m} {X : Set k} {Y : Set l} {Z : Set m} where

  EquivPreComp : {f : X → Y} → Equiv f → Equiv (preComp f {Z = Z})
  EquivPreComp record { hinv₁ = g₁ ;
                        hinvLeft = hinvLeft ;
                        hinv₂ = g₂ ;
                        hinvRight = hinvRight }
             = record { hinv₁ = preComp g₂ ;
                        hinvLeft = λ h → hfunext (λ x → hap h (hinvRight x)) ; 
                        hinv₂ = preComp g₁ ;
                        hinvRight = λ h → hfunext (λ y → hap h (hinvLeft y) ) } 

  
  EquivPostComp : {f : X → Y} → Equiv f → Equiv (postComp f {Z = Z})
  EquivPostComp record { hinv₁ = g₁ ;
                         hinvLeft = hinvLeft ;
                         hinv₂ = g₂ ;
                         hinvRight = hinvRight }
              = record { hinv₁ = postComp g₁ ;
                         hinvLeft = λ h → hfunext (λ z → hinvLeft (h z)) ;
                         hinv₂ = postComp g₂ ;
                         hinvRight = λ h → hfunext (λ z → hinvRight (h z)) }


module _ {k l} {X : Set k} {Y : Set l} where

  EquivTrivialFib : {f : X → Y} → TrivialFibration f → Equiv f
  EquivTrivialFib {f} record { isFib = fibp ;
                               isContr = contrp }
                = let g = λ (y : Y) → fibre.point (Contr.center contrp)
                  in record { hinv₁ = g ;
                              hinvLeft = λ y → cstPath (≡Sym (fibre.equal (Contr.center contrp)));
                              hinv₂ = g ;
                              hinvRight = λ x → hap fibre.point (inv {{fibp}} (Contr.path contrp (x , refl))) } 


  Equiv≡ext : {f g : X → Y} → ((x : X) → f x ≡ g x) → Equiv f → Equiv g
  Equiv≡ext Hyp record { hinv₁ = g₁ ;
                         hinvLeft = hinvLeft ;
                         hinv₂ = g₂ ;
                         hinvRight = hinvRight }
              = record { hinv₁ = g₁ ;
                         hinvLeft = λ y → endpointPath (hinvLeft y) refl (Hyp _) ;
                         hinv₂ = g₂ ;
                         hinvRight = λ x → endpointPath (hinvRight x) refl (ap g₂ (Hyp _)) }



--Results about fibrancy

module finiteProductFibrant {k} {X : Set k} {{_ : Fib X}} where

  open import FiniteSet

  finiteProdFib : {n : ℕ} → Fib (Prod X n)
  finiteProdFib {O} = ⊤Fib
  finiteProdFib {s n} = ΣFib {{fibB = finiteProdFib}}

  fibFiniteCanonical : ∀ {n : ℕ} → Fib (Fin n → X)
  fibFiniteCanonical {n} = ≅Fib {X = Prod X n}
                                (record { isoFun = prodFun ; isIso = isoProdFun })
                                {{finiteProdFib}}

  instance
    FiniteCofib : {A : Set} {{_ : FOSet A}} → Fib (A → X)
    FiniteCofib {{ record { cardinal = card ; funFO = f ; isIsoFO = isof } }} =
                ≅Fib {X = Fin card → X}
                     (record { isoFun = preComp f ;
                               isIso = isoPreComp isof })
                     {{fibFiniteCanonical}}


open finiteProductFibrant using (FiniteCofib)


totalSpaceFib : ∀ {k l} {X : Set k} {Y : Set l} {p : X → Y} {{_ : Fibration p}} → {{_ : Fib Y}} → Fib X
totalSpaceFib {Y = Y} {p = p} = ≅Fib {X = Σ Y (λ y → fibre p y)}
                                     (record { isoFun = λ {(y , (x , eq)) → x} ;
                                               isIso = record { inv = λ x → (p x) , (x , refl) ;
                                                                invLeft = λ _ → refl ;
                                                                invRight = λ {(y , (x , refl)) → refl} } })




--Results about contractibility


--There is a bit of redundance here

ContrSingAux : ∀ {k} {X : Set k} {x y₁ y₂ : X} {p₁ : Path X x y₁} {p₂ : Path X x y₂}
               → y₁ ≡ y₂ → ((i : I) → p₁ $ i ≡ p₂ $ i) → Equal (Σ X (Path X x))(y₁ , p₁) (y₂ , p₂)
ContrSingAux refl hyp = ap (λ p → _ , p) (≡Path hyp)

ContrSing : ∀ {k} {X : Set k} {x : X} → Contr (Σ X (λ y → Path X x y))
ContrSing {x = x} = record { center = x , hrefl ;
                             path = λ { (y , p) → [ (λ i → (p $ i) , [ (λ j → p $ (i ⊓ j)) ,
                                                                       ≡Trans (ap (λ i₁ → p $ i₁) ⊓right₀) (eqe₀ p) ,
                                                                       ap (λ i₁ → p $ i₁) ⊓right₁ ]) ,
                                                    ContrSingAux (eqe₀ p) (λ i → ≡Trans (ap (λ i₁ → p $ i₁) ⊓left₀) (eqe₀ p)) ,
                                                    ContrSingAux (eqe₁ p) (λ i → ap (λ i₁ → p $ i₁) ⊓left₁) ]} }


postulate
  ContrHfibreEquiv : ∀ {k l} {X : Set k} {Y : Set l} {f : X → Y} → Equiv f → {y : Y} → Contr (hfibre f y)

{-ContrHfibreEquiv record { hinv₁ = g₁ ;
                          hinvLeft = hinv₁ ;
                          hinv₂ = g₂ ;
                          hinvRight = hinv₂ }
               = record { center = {!!} ;
                          path = {!!} } 
-}



≅Contr : ∀ {k l} {X : Set k} {Y : Set l} → X ≅ Y → Contr X → Contr Y

≅Contr record { isoFun = f ;
                isIso = record { inv = g ;
                                 invLeft = invLeft ;
                                 invRight = _ } }
       record { center = x ;
                path = contrX }
     = record { center = f x ;
                path = λ y → let p = contrX (g y) in
                                [ (λ i → f (p $ i)) ,
                                  (ap f (eqe₀ p)) ,
                                  ≡Trans (ap f (eqe₁ p)) (≡Sym (invLeft y)) ] }


ΠContr : ∀ {k l} {X : Set k} {P : X → Set l} → ((x : X) → Contr (P x)) → Contr ((x : X) → P x)

ΠContr contrP = record { center = λ x → Contr.center (contrP x) ;
                         path = λ f → let p = λ x → Contr.path (contrP x) (f x) in
                                     [ (λ i x → (p x) $ i) ,
                                       funext (λ x → eqe₀ (p x)) ,
                                       funext (λ x → eqe₁ (p x)) ] } 





--results of factorisation for fibrant types

module _ {k l} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}} (f : X → Y) where

  record cocylinder : Set (k ⊔ l) where
    constructor cyl_,_,_
    field
      piX : X
      piY : Y
      path : Path Y (f piX) piY

  incCyl : X → cocylinder
  incCyl x = cyl x , (f x) , hrefl

  projCyl : cocylinder → Y
  projCyl = cocylinder.piY

  secCyl : cocylinder → X
  secCyl = cocylinder.piX


module _ {k l} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}} {f : X → Y} where

  ≅Cocylinder : Σ X (λ x → Σ Y (λ y → Path Y (f x) y)) ≅ cocylinder f
  ≅Cocylinder = record { isoFun = λ { (x , (y , p)) → cyl x , y , p} ;
                         isIso = record { inv = λ { (cyl x , y , p) → x , (y , p)} ;
                                          invLeft = λ { (cyl _ , _ , _) → refl} ;
                                          invRight = λ { (_ , (_ , _)) → refl} } }
                                          
  instance
    FibCocylinder : Fib (cocylinder f)
    FibCocylinder = ≅Fib ≅Cocylinder


  ≡cocylinder : {x₁ x₂ : X} {y₁ y₂ : Y} {p₁ : Path Y (f x₁) y₁} {p₂ : Path Y (f x₂) y₂}
                → x₁ ≡ x₂ → y₁ ≡ y₂ → ((i : I) → p₁ $ i ≡ p₂ $ i)
                → (cyl x₁ , y₁ , p₁) ≡ (cyl x₂ , y₂ , p₂)
  ≡cocylinder refl refl hyp = ap (λ p → cyl _ , _ , p) (≡Path hyp)


  ≅FibreProjCyl : {y : Y} → hfibre f y ≅ fibre (projCyl f) y
  ≅FibreProjCyl {y} = record { isoFun = λ { (x , p) → (cyl x , y , p) , refl} ;
                                 isIso = record { inv = λ { ((cyl x , y , p) , refl) → x , p} ;
                                                  invLeft = λ { ((cyl piX , piY , path) , refl) → refl} ;
                                                  invRight = λ {(x , p) → refl } } }

  FibrationProjCyl : Fibration (projCyl f)
  FibrationProjCyl = ≅Fib ≅FibreProjCyl

  EquivIncCyl : Equiv (incCyl f)
  EquivIncCyl = record { hinv₁ = secCyl f ;
                         hinvLeft = λ { (cyl x , y , p) → inv [ (λ i → cyl x , (p $ i) , [ (λ j → p $ (i ⊓ j)) ,
                                                                                           ≡Trans (ap (λ i₁ → p $ i₁) ⊓right₀) (eqe₀ p) ,
                                                                                           ap (λ i₁ → p $ i₁) ⊓right₁ ]) ,
                                                                ≡cocylinder refl (eqe₀ p) (λ i → ≡Trans (ap (λ i₁ → p $ i₁) ⊓left₀) (eqe₀ p)) ,
                                                                ≡cocylinder refl (eqe₁ p) (λ i → (ap (λ i₁ → p $ i₁) ⊓left₁)) ]} ;
                         hinv₂ = secCyl f ;
                         hinvRight = λ x → hrefl }

  ≅FibreSecCyl : {x : X} → Σ Y (λ y → Path Y (f x) y) ≅ fibre (secCyl f) x
  ≅FibreSecCyl {x} = record { isoFun = λ { (y , p) → (cyl x , y , p) , refl} ;
                              isIso = record { inv = λ { ((cyl _ , y , p) , refl) → y , p} ;
                                               invLeft = λ { ((cyl _ , _ , _) , refl) → refl} ;
                                               invRight = λ { (_ , _) → refl} } }

  TrivFibSecCyl : TrivialFibration (secCyl f)
  TrivFibSecCyl = record { isFib = ≅Fib ≅FibreSecCyl ;
                           isContr = ≅Contr ≅FibreSecCyl ContrSing }

  TrivFibProjCyl : Equiv f → TrivialFibration (projCyl f)
  TrivFibProjCyl equivf = record { isFib = FibrationProjCyl ;
                                   isContr = ≅Contr (≅FibreProjCyl) (ContrHfibreEquiv equivf) }
