{-# OPTIONS --rewriting #-}


module FibrantUniverse where


open import Data
open import Agda.Primitive




--This module will contains the fibrant universes and their homotopical structure. 



--Here we write every postulate for the fibrant universes
--Question :  is  Fib Set k → Set is okay ?

postulate
  I : Set
  e₀ e₁ : I
  _∩_ : I → I → I
  _∪_ : I → I → I
  
infixl 32 _∩_

postulate
  ∩left₀ : {i : I} → e₀ ∩ i ≡ e₀
  ∩right₀ : {i : I} → i ∩ e₀ ≡ e₀
  ∩left₁ : {i : I} → e₁ ∩ i ≡ i 
  ∩right₁ : {i : I} → i ∩ e₁ ≡ i


record dPath {k} (P : I → Set k) (x : P e₀) (y : P e₁) : Set k where
  constructor [_,_,_]
  field
    dpath : (i : I) → P i
    deq₀ : dpath e₀ ≡ x
    deq₁ : dpath e₁ ≡ y


mkPath : ∀ {k} {P : I → Set k} {x : P e₀} {y : P e₁}
         (f : (i : I) → P i) → f e₀ ≡ x → f e₁ ≡ y → dPath P x y
mkPath f eq₀ eq₁ = [ f , eq₀ , eq₁ ]


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
  (C : (I → X) → Set l) {{_ : {p : I → X} → Fib (C p)}} 
  (d : (x : X) → C (λ i → x)) where
  postulate
    J : (p : I → X) → C p
    Jcompute : (x : X) → J (λ i → x) ↦ d x
    {-# REWRITE Jcompute #-}




--A kind of weird fibrancy result

module _ {k l} {A : Set k} {{_ : Fib A}} {B : A → Set l} {{_ : {a : A} → Fib (B a)}} where

  ≅ImpAux : ((a : A) → B a) ≅ ({a : A} → B a)
  ≅ImpAux = record { isoFun = λ f → λ {x} → f x ;
                     isIso = record { inv = λ f x → f {x} ;
                                      invLeft = λ _ → refl ;
                                      invRight = λ _ → refl } }

  instance
    ΠFibImp : Fib ({a : A} → B a)
    ΠFibImp = ≅Fib ≅ImpAux




--Now we give definition of paths

Path : ∀ {k} (X : Set k) (x y : X) → Set k
Path X x y = dPath (λ _ → X) x y

_~~>_ : ∀ {k} {X : Set k} (x y : X) → Set k
x ~~> y = Path _ x y

infix 34 _~~>_


_$_ : ∀ {k} {P : I → Set k} {x : P e₀} {y : P e₁} → dPath P x y → (i : I) → P i
p $ i  = (dPath.dpath p) i

infix 35 _$_

eqe₀ : ∀ {k} {P : I → Set k} {x : P e₀} {y : P e₁} (p : dPath P x y) → p $ e₀ ≡ x
eqe₀ p = dPath.deq₀ p

eqe₁ : ∀ {k} {P : I → Set k} {x : P e₀} {y : P e₁} (p : dPath P x y) → p $ e₁ ≡ y
eqe₁ p = dPath.deq₁ p


module _ {k} {P : I → Set k} {x : P e₀} {y : P e₁} where


  ≡dPathAux : {p q : (i : I) → P i} {eqp₀ : p e₀ ≡ x} {eqp₁ : p e₁ ≡ y} {eqq₀ : q e₀ ≡ x} {eqq₁ : q e₁ ≡ y}
             → p ≡ q → [ p , eqp₀ , eqp₁ ] ≡ [ q , eqq₀ , eqq₁ ]
             
  ≡dPathAux {p = p} refl = ap₂ (λ e₁ e₂ → [ p , e₁ , e₂ ]) UIP UIP


  ≡dPath : {p q : dPath P x y}
           → ((i : I) → p $ i ≡ q $ i) → p ≡ q
           
  ≡dPath {p = [ p , deqp₀ , deqp₁ ]} {[ q , deqq₀ , deqq₁ ]} hyp = ≡dPathAux (funext (hyp))




--Basic properties of paths

module _ {k} {X : Set k} where

  hrefl : {x : X} → x ~~> x
  hrefl {x} = [ (λ i → x) , refl , refl ]


  cstPath : {x y : X} → x ≡ y → x ~~> y
  cstPath {x} = λ p → [ (λ i → x) , refl , p ]


  endpointPath : {x₁ x₂ y₁ y₂ : X} → x₁ ~~> y₁
                 → x₁ ≡ x₂ → y₁ ≡ y₂ → x₂ ~~> y₂

  endpointPath p eq₁ eq₂ = [ (λ i → p $ i) ,
                      ≡Trans (eqe₀ p) eq₁ ,
                      ≡Trans (eqe₁ p) eq₂ ]


  ≡PathAux : {x y : X} {p q : I → X} {eqp₀ : p e₀ ≡ x} {eqp₁ : p e₁ ≡ y} {eqq₀ : q e₀ ≡ x} {eqq₁ : q e₁ ≡ y}
             → p ≡ q → [ p , eqp₀ , eqp₁ ] ≡ [ q , eqq₀ , eqq₁ ]

  ≡PathAux {p = p} refl = ap₂ (λ e₁ e₂ → [ p , e₁ , e₂ ]) UIP UIP


  ≡Path : {x y : X} → {p q : x ~~> y} → ((i : I) → p $ i ≡ q $ i) → p ≡ q
  
  ≡Path {p = [ p , eqp₀ , eqp₁ ]} {[ q , eqq₀ , eqq₁ ]} hyp = ≡PathAux (funext hyp)


module _ {k} {X : Set k} {{_ : Fib X}} where

  JPath : ∀ {l} (C : {x y : X} → (p : x ~~> y) → Set l)
          {{_ : {x y : X} → {p : x ~~> y} → Fib (C p)}}
          → (d : (x : X) → C (hrefl {x = x}))
          → {x y : X} (p : x ~~> y) → C p

  JPath C d [ p , refl , refl ] = J (λ p₁ → C [ p₁ , refl , refl ]) (λ x → d x) p


  htransport : ∀ {l} (P : X → Set l) {{_ : {x : X} → Fib (P x)}}
              {x y : X} → x ~~> y → P x → P y

  htransport P = JPath _ (λ _ a → a)



{-
  module testingRewriting {l} (P : X → Set l) {{_ : {x : X} → Fib (P x)}}
                     {x y : X} {tx : P x} where
    
         test1 : htransport P hrefl tx ≡ tx
         test1 = refl
-}


module _ {k} {X : Set k} {{_ : Fib X}} where

  inv : {x y : X} → x ~~> y → y ~~> x
  inv = JPath _ (λ _ → hrefl)

  PathTrans : {x y z : X} → x ~~> y → y ~~> z → x ~~> z
  PathTrans = JPath _ (λ _ q → q) 

  _#_ : {x y z : X} → x ~~> y → y ~~> z → x ~~> z
  p # q = PathTrans p q

  infix 47 _#_

  #Nat : {x y z : X} {p₁ p₂ : x ~~> y} {q₁ q₂ : y ~~> z} → p₁ ~~> p₂ → q₁ ~~> q₂ → p₁ # q₁ ~~> p₂ # q₂
  #Nat {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂} r₁ r₂ = htransport (λ p → p₁ # q₁ ~~> p # q₂) r₁
                                                        (htransport (λ q → p₁ # q₁ ~~> p₁ # q) r₂ hrefl)

  #Hrefl : {x y : X} {p : x ~~> y} → p # hrefl ~~> p
  #Hrefl {p = p} = JPath (λ {x} {y} p → p # hrefl ~~> p) (λ _ → hrefl) p

  #InvRight : {x y : X} {p : x ~~> y} → p # inv p ~~> hrefl
  #InvRight {p = p} = JPath (λ p → p # inv p ~~> hrefl) (λ _ → hrefl) p

  #InvLeft : {x y : X} {p : x ~~> y} → inv p # p ~~> hrefl
  #InvLeft {p = p} = JPath (λ p → inv p # p ~~> hrefl) (λ _ → hrefl) p

  #Assoc : {x₁ x₂ x₃ x₄ : X} {p : x₁ ~~> x₂} {q : x₂ ~~> x₃} {r : x₃ ~~> x₄}
           → p # (q # r) ~~> (p # q) # r
  #Assoc {p = p} {q = q} {r = r} = JPath (λ {x₁} {x₂} p → {x₃ x₄ : X} → {q : x₂ ~~> x₃} → {r : x₃ ~~> x₄} → p # (q # r) ~~> (p # q) # r)
                                         (λ _ → hrefl) p 


module _ {k} {X : Set k} {{_ : Fib X}} where

  #Left : {x₁ x₂ x₃ : X} {p : x₁ ~~> x₂} {q₁ q₂ : x₂ ~~> x₃} → p # q₁ ~~> p # q₂ → q₁ ~~> q₂
  #Left {x₃ = x₃} {p = p} = JPath
                              (λ {x} {y} p₁ →
                                 {q₁ q₂ : y ~~> x₃} → p₁ # q₁ ~~> p₁ # q₂ → q₁ ~~> q₂)
                              (λ _ r → r) p

  #Right : {x₁ x₂ x₃ : X} {p : x₂ ~~> x₃} {q₁ q₂ : x₁ ~~> x₂} → q₁ # p ~~> q₂ # p → q₁ ~~> q₂
  #Right {x₁ = x₁} {p = p} = JPath
                              (λ {x} {y} p →
                                 {q₁ q₂ : x₁ ~~> x} → q₁ # p ~~> q₂ # p → q₁ ~~> q₂)
                              (λ _ r → ((inv #Hrefl) # r) # #Hrefl) p

  #invElim : {x₁ x₂ x₃ : X} {p₁ : x₁ ~~> x₂} {p₂ : x₂ ~~> x₃} {p₃ : x₁ ~~> x₃} → p₁ # p₂ ~~> p₃ → p₁ ~~> p₃ # inv p₂
  #invElim {p₂ = p₂} r = #Right {p = p₂} (r # (inv (#Hrefl) # ((#Nat hrefl (inv #InvLeft)) # #Assoc)))




module _ {k l} {X : Set k} {Y : Set l} where

  hap : (f : X → Y) {x y : X} → x ~~> y → (f x) ~~> (f y) 
  hap f p = [ (λ i → f (p $ i)) ,
              ap f (eqe₀ p) ,
              ap f (eqe₁ p) ]

  hfunext : {f g : X → Y} → ((x : X) → (f x) ~~> (g x)) → f ~~> g
  hfunext Hyp = [ (λ i x → (Hyp x) $ i) ,
                  funext (λ x → eqe₀ (Hyp x)) ,
                  funext (λ x → eqe₁ (Hyp x)) ]



--results about hap

hapComp : ∀ {k l m} {X : Set k} {Y : Set l} {Z : Set m}
          {f : X → Y} {g : Y → Z} {x y : X} {p : x ~~> y}
          → hap (g o f) p ≡ hap g (hap f p)

hapComp = ≡Path (λ _ → refl)


module _ {k l} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}} {f : X → Y} where


  hap# : {x y z : X} {p : x ~~> y} {q : y ~~> z}
         → hap f (p # q) ~~> hap f p # hap f q

  hap# {p = p} {q = q} = JPath (λ {x} {y} p → {q : y ~~> _}
                                  → hap f (p # q) ~~> hap f p # hap f q)
                               (λ _ → hrefl) p


  hapInv : {x y : X} {p : x ~~> y}
           → hap f (inv p) ~~> inv (hap f p) 

  hapInv {p = p} = JPath (λ p → hap f (inv p) ~~> inv (hap f p)) (λ _ → hrefl) p




--Define contractibility

record Contr {k} (X : Set k) : Set k where
  field
    center : X
    path : (y : X) → center ~~> y




--Homotopical properties of maps between types

module _ {k l} {X : Set k} {Y : Set l} (f : X → Y) where


  record fibre (y : Y) : Set (k ⊔ l) where
    constructor _,_
    field
      point : X
      equal : f point ≡ y


  --We do not use record because we want hfibre to be fibrant using ΣFib

  hfibre : (y : Y) → Set (k ⊔ l)
  hfibre y = Σ X (λ x → (f x) ~~> y)


  Fibration : Set (k ⊔ l)
  Fibration = {y : Y} → Fib (fibre y)

  ContrMap : Set (k ⊔ l)
  ContrMap = {y : Y} → Contr (fibre y)

  record TrivialFibration : Set (k ⊔ l) where
    field
      isFib : Fibration
      isContr : ContrMap


--Various logically equivalent (but not isomorphic) defintions of equivalence

  record Equiv : Set (k ⊔ l) where
    field
      hinv₁ : Y → X
      hinvLeft : (y : Y) → y ~~> (f (hinv₁ y))
      hinv₂ : Y → X
      hinvRight : (x : X) → x ~~> (hinv₂ (f x))


  record QEquiv : Set (k ⊔ l) where
    field
      hinv : Y → X
      hinvLeft : (y : Y) → y ~~> f (hinv y)
      hinvRight : (x : X) → x ~~> hinv (f x)

  record adjEquiv : Set (k ⊔ l) where
    field
      hinv : Y → X
      hinvLeft : (y : Y) → y ~~> f (hinv y)
      hinvRight : (x : X) → x ~~> hinv (f x)
      zig : (x : X) → hinvLeft (f x) ~~> hap f (hinvRight x)




--Results about equivalences




--Equivalence implies adjoint equivalences


module _ {k} {X : Set k} {{_ : Fib X}} {g : X → X} (ε : (x : X) → x ~~> g x) where


  naturalityε : {x₁ x₂ : X} {p : x₁ ~~> x₂}
                → p # ε x₂ ~~> ε x₁ # hap g p

  naturalityε {p = p} = JPath (λ {x} {y} p → p # ε y ~~> ε x # hap g p) (λ x → inv #Hrefl) p


  naturalityεAux : {x : X} → ε (g x) ~~> hap g (ε x)

  naturalityεAux {x = x} = #Left {p = ε x} naturalityε


module _ {k l} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}}
         {f : X → Y} where

       QEquivEquiv : Equiv f → QEquiv f

       QEquivEquiv record { hinv₁ = g₁ ;
                            hinvLeft = ε ;
                            hinv₂ = g₂ ;
                            hinvRight = η }
                            
                 = record { hinv = g₁ ;
                            hinvLeft = ε ;
                            hinvRight =  λ x → (η x # hap g₂ (ε (f x))) # inv (η (g₁ (f x))) }


       adjEquivQEquiv : QEquiv f → adjEquiv f

       adjEquivQEquiv record { hinv = g ; hinvLeft = ε ; hinvRight = η }

                     = record { hinv = g ;
                                hinvLeft = ε ;
                                hinvRight = λ x → (η x # hap g (ε (f x))) # inv (η (g (f x))) ;
                                zig = λ x → PathTrans
                                              {y = hap f (η x # hap g (ε (f x))) # inv (hap f (η (g (f x))))}
                                              (#invElim {p₁ = ε (f x)} {p₂ = hap f (η (g (f x)))} {p₃ = hap f (η x # hap g (ε (f x)))}
                                                        (PathTrans {y = ε (f x) # hap (f o g) (hap f (η x))}
                                                             (#Nat {q₁ = hap f (η (g (f x)))} {q₂ = hap (f o g) (hap f (η x))}
                                                                hrefl (PathTrans {y = hap f (hap (g o f) (η x))}
                                                                           (hap (hap f) (naturalityεAux η))
                                                                           (cstPath (≡Path (λ _ → refl)))))
                                                             (PathTrans {y = hap f (η x) # ε (f (g (f x)))}
                                                                  (inv (naturalityε ε))
                                                                  (PathTrans {y = hap f (η x) # hap f (hap g (ε (f x)))}
                                                                       (#Nat {q₁ = ε (f (g (f x)))} {q₂ = hap f (hap g (ε (f x)))}
                                                                             hrefl
                                                                             (PathTrans {y = hap (f o g) (ε (f x))}
                                                                                  (naturalityεAux ε)
                                                                                  (cstPath (≡Path (λ _ → refl)))))
                                                                       (inv hap#)))))
                                              (PathTrans (#Nat hrefl (inv hapInv)) (inv hap# )) }



       adjEquivEquiv : Equiv f → adjEquiv f
       
       adjEquivEquiv equivf = adjEquivQEquiv (QEquivEquiv equivf)




--hap and equivalences

module _ {k l} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}}
         {f : X → Y} where
               
       EquivHapAux : adjEquiv f → {x y : X} → Equiv (hap f {x = x} {y = y})
       
       EquivHapAux record { hinv = g ; hinvLeft = ε ; hinvRight = η ; zig = zig }
                   {x = x} {y = y}
                   = let hapinv : {x y : X} → f x ~~> f y → x ~~> y
                         hapinv = λ {x} {y} p → (η x # hap g p) # inv (η y)
                      in
                      record { hinv₁ = hapinv ;

                               hinvLeft = λ p → PathTrans {y = p # hrefl}
                                                    (inv #Hrefl)
                                                    (PathTrans {y = p # (ε (f y) # inv (ε (f y)))}
                                                         (#Nat hrefl (inv #InvRight))
                                                         (PathTrans {y = (p # ε (f y)) # inv (ε (f y))}
                                                              #Assoc
                                                              (PathTrans {y = (ε (f x) # hap (f o g) p) # inv (hap f (η y))}
                                                                   (#Nat (naturalityε ε)
                                                                         (hap inv (zig y)))
                                                                   (PathTrans {y = (hap f (η x) # hap f (hap g p)) # hap f (inv (η y))}
                                                                        (#Nat (#Nat (zig x)
                                                                                    (cstPath hapComp))
                                                                              (inv hapInv))
                                                                        (PathTrans {y = hap f (η x # hap g p) # hap f (inv (η y))}
                                                                             (#Nat (inv hap#) hrefl)
                                                                             (inv hap#)))))) ;

                               hinv₂ = hapinv ;

                               hinvRight = JPath (λ {x₁} {y₁} p₁ → p₁ ~~> hapinv (hap f {x = x₁} {y = y₁} p₁))
                                                 λ _ → PathTrans {y = η _ # inv (η _)}
                                                                 (inv #InvRight)
                                                                 (#Nat (inv #Hrefl) hrefl) }


       EquivHap : {x y : X} → Equiv f → Equiv (hap f {x = x} {y = y})
       
       EquivHap equivf = EquivHapAux (adjEquivEquiv equivf)



--Equivalence obeys two out of three

module _ {k l m} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}} {Z : Set m} {{_ : Fib Z}} where


  EquivComp : {f : X → Y} {g : Y → Z} → Equiv f → Equiv g → Equiv (g o f)
  
  EquivComp {f} {g}
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
  
  EquivTwoThreeRight {f = f} {g = g}
                     equivg
                     record { hinv₁ = gf₁ ;
                              hinvLeft = hinvgf₁ ;
                              hinv₂ = gf₂ ;
                              hinvRight = hinvgf₂ }
                   = record { hinv₁ = gf₁ o g ;
                              hinvLeft = λ y → Equiv.hinv₁ (EquivHap equivg) (hinvgf₁ (g y)) ; 
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


--We show A → X fibrant for A finite and X fibrant

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



--We show the total space of a fibration with fibrant base is fibrant

totalSpaceFib : ∀ {k l} {X : Set k} {Y : Set l} {p : X → Y}
                {{_ : Fibration p}} → {{_ : Fib Y}} → Fib X

totalSpaceFib {Y = Y} {p = p} = ≅Fib {X = Σ Y (λ y → fibre p y)}
                                     (record { isoFun = λ {(y , (x , eq)) → x} ;
                                               isIso = record { inv = λ x → (p x) , (x , refl) ;
                                                                invLeft = λ _ → refl ;
                                                                invRight = λ {(y , (x , refl)) → refl} } })




--Results about contractibility


--There is a bit of redundance here


ContrSingAux : ∀ {k} {X : Set k} {x y₁ y₂ : X} {p₁ : x ~~> y₁} {p₂ : x ~~> y₂}
               → y₁ ≡ y₂ → ((i : I) → p₁ $ i ≡ p₂ $ i) → Equal (Σ X (Path X x)) (y₁ , p₁) (y₂ , p₂)
               
ContrSingAux refl hyp = ap (λ p → _ , p) (≡Path hyp)


ContrSing : ∀ {k} {X : Set k} {x : X} → Contr (Σ X (λ y → x ~~> y))

ContrSing {x = x} = record { center = x , hrefl ;
                             path = λ { (y , p) → [ (λ i → (p $ i) , [ (λ j → p $ (i ∩ j)) ,
                                                                       ≡Trans (ap (λ i₁ → p $ i₁) ∩right₀) (eqe₀ p) ,
                                                                       ap (λ i₁ → p $ i₁) ∩right₁ ]) ,
                                                    ContrSingAux (eqe₀ p) (λ i → ≡Trans (ap (λ i₁ → p $ i₁) ∩left₀) (eqe₀ p)) ,
                                                    ContrSingAux (eqe₁ p) (λ i → ap (λ i₁ → p $ i₁) ∩left₁) ]} }




--Contractibility of Homotopy fibre

module _ {k l} {X : Set k} {{_ : Fib X}}
               {Y : Set l} {{_ : Fib Y}}
               {f : X → Y} where

       PathHfibre : {x₁ x₂ : X} {y : Y}
                  → (p : x₁ ~~> x₂) {p₁ : (f x₁) ~~> y} {p₂ : (f x₂) ~~> y}
                  → p₁ ~~> ((hap f p) # p₂) → Path (hfibre f y) (x₁ , p₁) (x₂ , p₂)

       PathHfibre {y = y} p r = JPath
                                   (λ {x₁} {x₂} p₁ →
                                      {p₂ : f x₁ ~~> y} {p₃ : f x₂ ~~> y} →
                                      p₂ ~~> hap f p₁ # p₃ → Path (hfibre f y) (x₁ , p₂) (x₂ , p₃))
                                   (λ x r → [ (λ i → x , [ (λ j → (r $ i) $ j) ,
                                                           (eqe₀ (r $ i)) ,
                                                           (eqe₁ (r $ i)) ]) ,
                                              equalΣ refl (≡Path (λ i → ap (λ p → p $ i) (eqe₀ r))) ,
                                              equalΣ refl (≡Path (λ i → ap (λ p → p $ i) (eqe₁ r))) ]) p r 


       ContrHfibreEquiv : Equiv f → {y : Y} → Contr (hfibre f y)

       ContrHfibreEquiv equivf {y = y} =

                 let x₁ = Equiv.hinv₁ equivf y in
                 let p₁ = Equiv.hinvLeft equivf y in

                 record { center = x₁ , inv (p₁) ;
                          path = λ { (x₂ , p₂) → PathHfibre (Equiv.hinv₁ (EquivHap equivf) (inv p₁ # inv p₂))
                                                   (PathTrans {y = inv p₁ # hrefl}
                                                        (inv #Hrefl)
                                                        (PathTrans {y = inv p₁ # (inv p₂ # p₂)}
                                                             (#Nat hrefl (inv #InvLeft))
                                                             (PathTrans {y = (inv p₁ # inv p₂) # p₂}
                                                                  #Assoc (#Nat {p₁ = inv p₁ # inv p₂}
                                                                               {p₂ = hap _ (Equiv.hinv₁ (EquivHap equivf) (inv p₁ # inv p₂))}
                                                                               (Equiv.hinvLeft (EquivHap equivf) (inv p₁ # inv p₂)) hrefl)))  ) } }





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





{-
We define the cocylinder fibration for fibrant types
It factors a map f between fibrant types as 
  • first the section (called incCyl) of a trivial fibration (called secCyl)
  • followed by a fibration (called projCyl)
Moreover projCyl is a trivial fibration if f si an equivalence
-}


module _ {k l} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}} (f : X → Y) where

  record cocylinder : Set (k ⊔ l) where
    constructor cyl_,_,_
    field
      piX : X
      piY : Y
      path : (f piX) ~~> piY

  incCyl : X → cocylinder
  incCyl x = cyl x , (f x) , hrefl

  projCyl : cocylinder → Y
  projCyl = cocylinder.piY

  secCyl : cocylinder → X
  secCyl = cocylinder.piX


module _ {k l} {X : Set k} {{_ : Fib X}} {Y : Set l} {{_ : Fib Y}} {f : X → Y} where


  ≅Cocylinder : Σ X (λ x → Σ Y (λ y → (f x) ~~> y)) ≅ cocylinder f
  
  ≅Cocylinder = record { isoFun = λ { (x , (y , p)) → cyl x , y , p} ;
                         isIso = record { inv = λ { (cyl x , y , p) → x , (y , p)} ;
                                          invLeft = λ { (cyl _ , _ , _) → refl} ;
                                          invRight = λ { (_ , (_ , _)) → refl} } }


  instance
    FibCocylinder : Fib (cocylinder f)
    
    FibCocylinder = ≅Fib ≅Cocylinder


  ≡cocylinder : {x₁ x₂ : X} {y₁ y₂ : Y} {p₁ : (f x₁) ~~> y₁} {p₂ : (f x₂) ~~> y₂}
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
                         hinvLeft = λ { (cyl x , y , p) → inv [ (λ i → cyl x , (p $ i) ,
                                                                [ (λ j → p $ (i ∩ j)) ,
                                                                  ≡Trans (ap (λ i₁ → p $ i₁) ∩right₀) (eqe₀ p) ,
                                                                  ap (λ i₁ → p $ i₁) ∩right₁ ]) ,
                                                                ≡cocylinder refl (eqe₀ p) (λ i → ≡Trans (ap (λ i₁ → p $ i₁) ∩left₀) (eqe₀ p)) ,
                                                                ≡cocylinder refl (eqe₁ p) (λ i → (ap (λ i₁ → p $ i₁) ∩left₁)) ]} ;
                         hinv₂ = secCyl f ;
                         hinvRight = λ x → hrefl }


  ≅FibreSecCyl : {x : X} → Σ Y (λ y → (f x) ~~> y) ≅ fibre (secCyl f) x
  
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

