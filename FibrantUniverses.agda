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
p $ i = (dPath.dpath p) i

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

  ≡Path : {x₁ x₂ y₁ y₂ : X} → Path X x₁ y₁ → x₁ ≡ x₂ → y₁ ≡ y₂ → Path X x₂ y₂
  ≡Path p eq₁ eq₂ = [ (λ i → p $ i) ,
                      ≡Trans (eqe₀ p) eq₁ ,
                      ≡Trans (eqe₁ p) eq₂ ]


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

  record fibre (y : Y) : Set (k ⊔ l) where
    constructor _,_
    field
      point : X
      equal : f point ≡ y

  Fibration : Set (k ⊔ l)
  Fibration = {y : Y} → Fib (fibre y)

  ContrMap : Set (k ⊔ l)
  ContrMap = (y : Y) → Contr (fibre y)

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
                = let g = λ (y : Y) → fibre.point (Contr.center (contrp y))
                  in record { hinv₁ = g ;
                              hinvLeft = λ y → cstPath (≡Sym (fibre.equal (Contr.center (contrp y))));
                              hinv₂ = g ;
                              hinvRight = λ x → hap fibre.point (inv {{fibp}} (Contr.path (contrp (f x)) (x , refl))) } 


  Equiv≡ext : {f g : X → Y} → ((x : X) → f x ≡ g x) → Equiv f → Equiv g
  Equiv≡ext Hyp record { hinv₁ = g₁ ;
                         hinvLeft = hinvLeft ;
                         hinv₂ = g₂ ;
                         hinvRight = hinvRight }
              = record { hinv₁ = g₁ ;
                         hinvLeft = λ y → ≡Path (hinvLeft y) refl (Hyp _) ;
                         hinv₂ = g₂ ;
                         hinvRight = λ x → ≡Path (hinvRight x) refl (ap g₂ (Hyp _)) }



--Results about fibrancy

open import FiniteSet

finiteProdFib : ∀ {k} {X : Set k} {{_ : Fib X}} {n : ℕ} → Fib (Prod X n)
finiteProdFib {n = O} = ⊤Fib
finiteProdFib {n = s n} = ΣFib {{fibB = finiteProdFib}}

fibFiniteCanonical : ∀ {n : ℕ} {k} {X : Set k} {{_ : Fib X}} → Fib (Fin n → X)
fibFiniteCanonical {n} {X = X} = ≅Fib {X = Prod X n}
                                      (record { isoFun = prodFun ; isIso = isoProdFun })
                                      {{finiteProdFib}}

instance
  FiniteCofib : ∀ {k} {A : Set} {{_ : FOSet A}} {X : Set k} {{_ : Fib X}} → Fib (A → X)
  FiniteCofib {{ record { cardinal = card ; funFO = f ; isIsoFO = isof } }} {X} =
                ≅Fib {X = Fin card → X}
                     (record { isoFun = preComp f ;
                               isIso = isoPreComp isof })
                     {{fibFiniteCanonical}}


totalSpaceFib : ∀ {k l} {X : Set k} {Y : Set l} {p : X → Y} {{_ : Fibration p}} → {{_ : Fib Y}} → Fib X
totalSpaceFib {Y = Y} {p = p} = ≅Fib {X = Σ Y (λ y → fibre p y)}
                                     (record { isoFun = λ {(y , (x , eq)) → x} ;
                                               isIso = record { inv = λ x → (p x) , (x , refl) ;
                                                                invLeft = λ _ → refl ;
                                                                invRight = λ {(y , (x , refl)) → refl} } })




--Results about contractibility


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
