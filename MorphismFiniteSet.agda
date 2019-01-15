module MorphismFiniteSet where

open import Data
open import FiniteSet


{- We define morphisms between FOSet -}


isOrderPreserving : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} (f : A → B) → Set
isOrderPreserving {A} f = (x y : A) → x << y ↔ f x << f y


record HomFO {A B : Set} {{Afinite : FOSet A}} {{Bfinite : FOSet B}} (f : A → B) : Set where
  field
    isoHomFO : iso f
    orderPreserving : isOrderPreserving f

--open HomFO {{...}} public





{- We construct some basic examples of morphisms of FOSet -}


HomFOId : {A : Set} {{Afinite : FOSet A}} → HomFO (Id {A = A})

HomFOId = record { isoHomFO = isoId ; 
                   orderPreserving = λ x y → ↔Refl }


HomFOcanonical : {A : Set} {{_ : FOSet A}} → HomFO (funFO {A})

HomFOcanonical = record { isoHomFO = isIsoFO ;
                          orderPreserving = λ _ _ → ↔Refl }


HomFOcanonicalInv : {A : Set} {{_ : FOSet A}} → HomFO (iso.inv (isIsoFO {A}))

HomFOcanonicalInv {A} = record { isoHomFO = isoInv isIsoFO ;
                                 orderPreserving = λ x y → transport₂↔ _<<_ (iso.invLeft (isIsoFO {A}) _)
                                                                            (iso.invLeft (isIsoFO {A}) _) }


HomFOComp : {A B C : Set} {Afinite : FOSet A} {Bfinite : FOSet B} {Cfinite : FOSet C} 
            {f : A → B} {g : B → C}
            → HomFO {{Afinite}} {{Bfinite}} f
            → HomFO {{Bfinite}} {{Cfinite}} g
            → HomFO {{Afinite}} {{Cfinite}} (g o f)

HomFOComp record { isoHomFO = isof ; orderPreserving = orderf } 
          record { isoHomFO = isog ; orderPreserving = orderg } 
        = record { isoHomFO = isoComp isof isog ; 
                   orderPreserving = λ x y → ↔Trans _ (orderf _ _) (orderg _ _) }


HomFOΣfun : {A₁ A₂ : Set} {{_ : FOSet A₁}} {{_ : FOSet A₂}} 
              {B₁ : A₁ → Set} {{_ : {a₁ : A₁} → FOSet (B₁ a₁)}} {B₂ : A₂ → Set} {{_ : {a₂ : A₂} → FOSet (B₂ a₂)}}
              {f : A₁ → A₂} (homf : HomFO f)
              {F : {a₁ : A₁} → B₁ a₁ → B₂ (f a₁)} (homF : {a₁ : A₁} → HomFO (F {a₁}))
              → HomFO (Σfun {B₂ = B₂} f F)

HomFOΣfun {B₁ = B₁} {B₂ = B₂} {f = f} record { isoHomFO = isof ; orderPreserving = orderf } {F = F} homF
               = record { isoHomFO = isoΣfun isof (λ a₁ → HomFO.isoHomFO {f = F {a₁}} (homF {a₁})) ; 
                          orderPreserving = λ {(a₁ , b₁) (a₂ , b₂) 
                                            → ↔Trans (Σord a₁ b₁ a₂ b₂) 
                                                     (Σorder {B = B₁}) 
                                                     (↔Trans (Σord {B = B₂} (f a₁) (F b₁) (f a₂) (F b₂)) 
                                                              (∨Nat↔ (orderf _ _) 
                                                                     (↔Trans (Σ (a₁ ≡ a₂) (λ p → transport B₂ (ap f p) (F b₁) << F b₂))
                                                                        ((λ {(refl , q) → refl , ∧left (HomFO.orderPreserving {f = F {a₁}} homF b₁ b₂) q}) , 
                                                                          λ {(refl , q) → refl , (∧right (HomFO.orderPreserving {f = F {a₁}} homF b₁ b₂) q)}) 
                                                                        (injectiveEqual (λ p → transport B₂ p (F b₁) << F b₂) (injectiveIso isof)))) 
                                                              (↔Sym (Σorder {B = B₂})))} }



{- We construct the isomorphism of finite sets needed for the definition of operads -}


η₁ : (B : Fin (s O) → Set) {{_ : {x : Fin (s O)} → FOSet (B x)}} → B fzero → Σ (Fin (s O)) B
η₁ B x = fzero , x

η₂ : (A : Set) {{_ : FOSet A}} → A → Σ A (λ _ → Fin (s O))
η₂ A a = a , fzero

ψ : (A : Set) {{_ : FOSet A}} (B : A → Set) {{_ : {a : A} → FOSet (B a)}}
    (C : Σ A B → Set) {{_ : {x : Σ A B} → FOSet (C x)}}
    → Σ A (λ a → Σ (B a) (λ b → C (a , b))) → Σ (Σ A B) C
ψ A B C (a  , (b , c)) = ((a , b) , c)          




 
HomFOη₁ : {B : Fin (s O) → Set} {{Bfinite : {x : Fin (s O)} → FOSet (B x)}} → HomFO (η₁ B)

HomFOη₁ {B} = record { isoHomFO = record { inv = λ {(fzero , q) → q} ; 
                                             invLeft = λ {(fzero , _) → refl} ; 
                                             invRight = λ _ → refl } ; 
                       orderPreserving = λ x y → ΣorderSnd {B = B} } 



HomFOη₂ : {A : Set} {{_ : FOSet A}} → HomFO (η₂ A)

HomFOη₂ = record { isoHomFO = record { inv = λ { (a , _) → a} ; 
                                       invLeft = λ { (a , fzero) → refl} ; 
                                       invRight = λ _ → refl } ;
                   orderPreserving = λ x y → ↔Trans (x << y ∨ Σ (x ≡ y) (λ _ → ord (Fin (s O)) fzero fzero)) 
                                                   ((λ q → left q) ,
                                                    (λ { (left q) → q ; (right (_ , ()) )}))
                                                   (↔Sym (Σorder {B = λ _ → Fin (s O)})) } 



HomFOψ : {A : Set} {{_ : FOSet A}} {B : A → Set} {{_ : {a : A} → FOSet (B a)}} 
           {C : Σ A B → Set} {{_ : {x : Σ A B} → FOSet (C x)}}
           → HomFO (ψ A B C)

HomFOψ {A} {B} {C} = record { isoHomFO = record { inv = λ {((a , b) , c) → (a , (b , c))} ; 
                                                    invLeft = λ {((a , b) , c) → refl} ; 
                                                    invRight = λ {(a , (b , c)) → refl} } ;
                                orderPreserving = λ { (a₁ , (b₁ , c₁)) (a₂ , (b₂ , c₂)) → 
                                    ↔Trans (Σord a₁ (b₁ , c₁) a₂ (b₂ , c₂))
                                      (Σorder {b₁ = (b₁ , c₁)} {b₂ = (b₂ , c₂)}) 
                                      (↔Trans (Σord (a₁ , b₁) c₁ (a₂ , b₂) c₂)
                                         (↔Trans (Σord a₁ b₁ a₂ b₂ ∨
                                                 Σ ((a₁ , b₁) ≡ (a₂ , b₂)) (λ p → transport C p c₁ << c₂))
                                                 (↔Trans
                                                    (a₁ << a₂ ∨
                                                      Σ (a₁ ≡ a₂) (λ p → Σord (transport B p b₁) (deptransport C p c₁) b₂ c₂))
                                                    (∨Nat↔ ↔Refl 
                                                           ((λ {(refl , q) → refl , ∧left (Σorder {a₁ = b₁} {b₁ = c₁}) q}) , 
                                                             λ {(refl , q) → refl , ∧right (Σorder {a₁ = b₁} {b₁ = c₁}) q})) 
                                                    ((λ { (left qa) → left (left qa) ; 
                                                          (right (refl , left qb)) → left (right (refl , qb)) ; 
                                                          (right (refl , right (refl , qc))) → right (refl , qc)}) , 
                                                      λ { (left (left qa)) → left qa ; 
                                                          (left (right (refl , qb))) → right (refl , (left qb)) ; 
                                                          (right (refl , qc)) → right (refl , (right (refl , qc)))}))
                                             (∨Nat↔ (↔Sym (Σorder {B = B})) 
                                                     ↔Refl)) 
                                             (↔Sym (Σorder {B = C})))} }







{- We show that being a morphism of FOSet is a property -}

Prop< : {n : ℕ} {a₁ a₂ : Fin n} → isProp (a₁ < a₂)
Prop< {.(s _)} {fzero} {fzero} = Prop⊥
Prop< {.(s _)} {fzero} {fsucc a₂} = Prop⊤
Prop< {.(s _)} {fsucc a₁} {fzero} = Prop⊥
Prop< {.(s _)} {fsucc a₁} {fsucc a₂} = Prop< {a₁ = a₁} {a₂ = a₂}


Prop<< : {A : Set} {{_ : FOSet A}} → {a₁ a₂ : A} → isProp (a₁ << a₂)
Prop<< {a₁ = a₁} {a₂ = a₂} = Prop< {a₁ = funFO a₁} {a₂ = funFO a₂}


PropOrderPreserving : {A B : Set} {{Afinite : FOSet A}} {{_ : FOSet B}} {f : A → B}
                      → isProp (isOrderPreserving f)
                      
PropOrderPreserving {A} {B} = Prop→ (Prop→ (Prop↔ (Prop<< {A}) (Prop<< {B}))) 


PropHomFOAux : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} {f : A → B} {homf₁ homf₂ : HomFO f}
               → HomFO.isoHomFO homf₁ ≡ HomFO.isoHomFO homf₂ → HomFO.orderPreserving homf₁ ≡ HomFO.orderPreserving homf₂
               → homf₁ ≡ homf₂
               
PropHomFOAux {homf₁ = record { isoHomFO = iso₁ ; orderPreserving = ord₁ }}
             {record { isoHomFO = iso₂ ; orderPreserving = ord₂ }}
             refl refl = refl


PropHomFO : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} {f : A → B} → isProp (HomFO f)

PropHomFO {A} {B} = PropHomFOAux PropIso (PropOrderPreserving {A} {B})




{- 
  Now we show some properties of morphism between canonical finite sets 
  Our main goal is to show that there is at most one morphism between any two FOSet, but we will need a lot of intermediary results
-}



{- First we define canonical finite set minus one element -}


--Fin- m y is set theoretically Fin m - {y}

Fin- : (m : ℕ) (y : Fin m) → Set
Fin- m y = Σ (Fin m) (λ x → ¬ (x ≡ y))


≡Fin- : {m : ℕ} {y : Fin m} → {n₁ n₂ : Fin- m y} → Σleft n₁ ≡ Σleft n₂ → n₁ ≡ n₂
≡Fin- {n₁ = a₁ , x₁} {a₂ , x₂} refl = equalΣ refl (funext (λ _ → Prop⊥))


--We will show that Fin (s m) - {y} is isomorphic to Fin m


--This is the isomorphism...

funFin- : {m : ℕ} (y : Fin (s m)) → Fin m → Fin- (s m) y
funFin- fzero fzero = fsucc fzero , λ ()
funFin- fzero (fsucc x) = (fsucc (fsucc x)) , λ ()
funFin- (fsucc y) fzero = fzero , λ ()
funFin- (fsucc y) (fsucc x) = (fsucc (Σleft (funFin- y x))) , λ p → Σright (funFin- y x) (injectiveFsucc p)


--...and its inverse

invFunFin- : {m : ℕ} (y : Fin (s m)) → Fin- (s m) y → Fin m
invFunFin- fzero (fzero , neq) = efql (neq refl)
invFunFin- fzero (fsucc x , neq) = x
invFunFin- (fsucc fzero) (fzero , neq) = fzero
invFunFin- (fsucc (fsucc y)) (fzero , neq) = fzero
invFunFin- (fsucc fzero) (fsucc x , neq) = fsucc (invFunFin- fzero (x , λ eq → neq (ap fsucc eq)))
invFunFin- (fsucc (fsucc y)) (fsucc x , neq) = fsucc (invFunFin- (fsucc y) (x , λ eq → neq (ap fsucc eq)))


--We check this works

invLeftFunFin- : {m : ℕ} (y : Fin (s m)) (x : Fin- (s m) y) → x ≡ funFin- y (invFunFin- y x)
invLeftFunFin- fzero (fzero , neq) = efql (neq refl)
invLeftFunFin- fzero (fsucc fzero , neq) = ≡Fin- refl 
invLeftFunFin- fzero (fsucc (fsucc x) , neq) = ≡Fin- refl
invLeftFunFin- (fsucc fzero) (fzero , neq) = ≡Fin- refl
invLeftFunFin- (fsucc (fsucc y)) (fzero , neq) = ≡Fin- refl 
invLeftFunFin- (fsucc fzero) (fsucc x , neq) = ≡Fin- (ap (fsucc o Σleft)
                                                         (invLeftFunFin- fzero (x , (λ eq → neq (ap fsucc eq)))))
invLeftFunFin- (fsucc (fsucc y)) (fsucc x , neq) = ≡Fin- (ap (fsucc o Σleft)
                                                             (invLeftFunFin- (fsucc y) (x , (λ eq → neq (ap fsucc eq)))))
                                                    


invRightFunFin- : {m : ℕ} (y : Fin (s m)) (x : Fin m) → x ≡ invFunFin- y (funFin- y x)
invRightFunFin- fzero fzero = refl
invRightFunFin- fzero (fsucc x) = refl
invRightFunFin- (fsucc fzero) fzero = refl
invRightFunFin- (fsucc (fsucc y)) fzero = refl
invRightFunFin- (fsucc fzero) (fsucc x) = ap fsucc (≡Trans {y = invFunFin- fzero (funFin- fzero x)}
                                                   (invRightFunFin- fzero x)
                                                   (ap (invFunFin- fzero)
                                                       {x = funFin- fzero x}
                                                       {y = (Σleft (funFin- fzero x) , _)}
                                                       (≡Fin- refl)))
invRightFunFin- (fsucc (fsucc y)) (fsucc x) = ap fsucc (≡Trans {y = invFunFin- (fsucc y) (funFin- (fsucc y) x)}
                                                   (invRightFunFin- (fsucc y) x)
                                                   (ap (invFunFin- (fsucc y))
                                                       {x = funFin- (fsucc y) x}
                                                       {y = (Σleft (funFin- (fsucc y) x) , _)}
                                                       (≡Fin- refl)))


isoFunFin- : {m : ℕ} {y : Fin (s m)} → iso (funFin- y)
isoFunFin- {y = y} = record { inv = invFunFin- _ ;
                              invLeft = invLeftFunFin- _ ;
                              invRight = invRightFunFin- y }




{- We prove some properties of morphisms between finite sets -}

surjectiveInjective : {m : ℕ} → {f : Fin m → Fin m} → injective f → surjective f
surjectiveInjective {O} _ = λ ()
surjectiveInjective {s m} {f} injf = let ffsucc : Fin m → Fin- (s m) (f fzero)
                                         ffsucc = λ x → (f (fsucc x)) , (λ eq → ≢FzeroFsucc (injf eq)) in
                                     let surjectiveFfsucc : surjective ffsucc
                                         surjectiveFfsucc = surjectivePostCompIso {g = invFunFin- (f fzero)}
                                                                                  (isoInv (isoFunFin-))
                                                                                  (surjectiveInjective
                                                                                  (λ eq → injectiveFsucc (injf
                                                                                          (ap Σleft
                                                                                          (isoCancel (isoInv (isoFunFin- {y = f fzero})) eq))))) in
                                     λ x → ∨Elim (λ {refl → fzero , refl})
                                                 (λ neq → let a = Σleft (surjectiveFfsucc (x , neq)) in
                                                          (fsucc a) , (ap Σleft (Σright (surjectiveFfsucc (x , neq)))))
                                                 (≡FinDecidable x (f fzero))


IsoCardinal : {m n : ℕ} {f : Fin m → Fin n} → iso f → n ≡ m

IsoCardinal {O} {O} _ = refl

IsoCardinal {O} {s n} isof = elimFinO (iso.inv isof fzero)

IsoCardinal {s m} {O} {f} = elimFinO (f fzero)

IsoCardinal {s m} {s n} {f} isof = let ffsucc : Fin m → Fin- (s n) (f fzero)
                                       ffsucc = λ x → (f (fsucc x)) , λ eq → ≢FzeroFsucc (isoCancel isof eq) in
                                   let isoFfsucc : iso ffsucc
                                       isoFfsucc = let h = iso.inv isof in
                                                   let funAux : (x : Fin (s n)) → ¬ (x ≡ f fzero) →  Σ (Fin m) (λ y → h x ≡ fsucc y)
                                                       funAux = λ x  neq → isSucc≡ {x = h x}
                                                                           λ eq → neq (≡Trans {y = f (h x)}
                                                                                      (iso.invLeft isof _)
                                                                                      (ap f (≡Sym eq))) in
                                                   record { inv = λ { (x , neq) → Σleft (funAux x neq)};
                                                            invLeft = λ {(x , neq) → ≡Fin- (isoCancel (isoInv isof)
                                                                                           (≡Trans {y = fsucc (Σleft (funAux x neq))}
                                                                                                   (Σright (funAux x neq))
                                                                                                   (iso.invRight isof _)))} ;
                                                            invRight = λ a → injectiveFsucc (≡Trans {y = h (f (fsucc a))}
                                                                                                    (iso.invRight isof _)
                                                                                                    (Σright (isSucc≡ (λ eq → ≢FzeroFsucc
                                                                                                                     (isoCancel isof (≡Trans
                                                                                                                     (iso.invLeft isof (f (fsucc a)))
                                                                                                                     (ap f (≡Sym eq)))))))) } in
                                   ap s (IsoCardinal {f = invFunFin- (f fzero) o ffsucc}
                                                     (isoComp isoFfsucc (isoInv (isoFunFin- {y = f fzero}))))




{- We show some properties of order preserving functions -}


--Order preserving functions are injetcive and surjective

injectiveOrderPreserving : {m : ℕ} {f : Fin m → Fin m} → isOrderPreserving f → injective f
injectiveOrderPreserving ordf {x = x} {y = y} p = <Total (λ ordxy → <IreflEqual p (∧left (ordf x y) ordxy))
                                                          λ ordyx → <IreflEqual (≡Sym p) (∧left (ordf y x) ordyx)

surjectiveOrderPreserving : {m : ℕ} {f : Fin m → Fin m} → isOrderPreserving f → surjective f
surjectiveOrderPreserving ordf = surjectiveInjective (injectiveOrderPreserving ordf) 


--Order preserving function preserve the smallest element

orderFzero : {m : ℕ} (f : Fin (s m) → Fin (s m)) → isOrderPreserving f → f fzero ≡ fzero

orderFzero f ordf = isFzero (λ y ordy → let a = Σleft (surjectiveOrderPreserving {f = f} ordf y) in
                                        let eqa : f a ≡ y
                                            eqa = Σright (surjectiveOrderPreserving {f = f} ordf y) in
                                        let orda : f a << f fzero
                                            orda = transport (λ x₁ → x₁ << f fzero) (≡Sym eqa) ordy in 
                                        <MinFzero {n = a} (∧right (ordf _ _) orda))



--The next three lemme show that there is only one funtion from Fin n to itself which is order preserving : the identity

HomFOfunction : {m : ℕ} (f : Fin (s m) → Fin (s m))
                → isOrderPreserving f → Fin m → Fin m

HomFOfunction f ordf x = Σleft (isSucc {x = f (fsucc x)} (transport (λ y → y << f (fsucc x)) (orderFzero f ordf)
                                                                    (∧left (ordf fzero (fsucc x)) *))) 


HomFOUniqueAux1 : {m : ℕ} (f : Fin (s m) → Fin (s m)) (ordf : isOrderPreserving f)
                  → {a : Fin m} → f (fsucc a) ≡ fsucc (HomFOfunction f ordf a)
HomFOUniqueAux1 f ordf {x} = Σright (isSucc {x = f (fsucc x)} (transport (λ y → y << f (fsucc x)) (orderFzero f ordf)
                                                                         (∧left (ordf fzero (fsucc x)) *))) 


HomFOUniqueCstCardinal : {m : ℕ} {f : Fin m → Fin m} → isOrderPreserving f → f ≡ Id

HomFOUniqueCstCardinal {O} {f = f} Hyp = funext (λ ()) 

HomFOUniqueCstCardinal {s n} {f = f} ordf = funext (λ { fzero → orderFzero f ordf ;
                                                      (fsucc a) → let g = HomFOfunction f ordf in
                                                                  ≡Trans {y = fsucc (g a)}
                                                                         (HomFOUniqueAux1 f ordf)
                                                                         (ap fsucc (≡fun (HomFOUniqueCstCardinal {f = g} λ x y →
                                                                                   (↔Trans (f (fsucc x) << f (fsucc y))
                                                                                           (ordf _ _)
                                                                                           (transport₂↔ _<<_ {a₁ = f (fsucc x)}
                                                                                                             {a₂ = fsucc (g x)}
                                                                                                             {b₁ = f (fsucc y)}
                                                                                                             {b₂ = fsucc (g y)}
                                                                                                        (HomFOUniqueAux1 f ordf)
                                                                                                        (HomFOUniqueAux1 f ordf))))))})



{- We show that morphisms between FOSet are unique -}


orderPreservingTransport : {m n : ℕ} (p : m ≡ n) {x y : Fin m} → x << y ↔ transport Fin p x << transport Fin p y
orderPreservingTransport refl = ↔Refl


--First we show for morphism between canonical finite sets, using the result for automorphism of canonical finite sets

HomFOUniqueCanonical : {m n : ℕ} {f g : Fin m → Fin n} (homf : HomFO f) (homg : HomFO g) → f ≡ g

HomFOUniqueCanonical {f = f} {g = g} homf homg = let p = IsoCardinal (HomFO.isoHomFO homf) in
                                                 isoCancel (isoPostComp (isoTransport Fin p))
                                                   (≡Trans {y = Id}
                                                           (HomFOUniqueCstCardinal λ x y → ↔Trans (f x << f y)
                                                                                          (HomFO.orderPreserving homf x y)
                                                                                          (orderPreservingTransport p {x = f x} {y = f y}))
                                                     (≡Sym (HomFOUniqueCstCardinal (λ x y → ↔Trans (g x << g y)
                                                                                           (HomFO.orderPreserving homg x y)
                                                                                           (orderPreservingTransport p {x = g x} {y = g y})))))
                                                                                           

--The main theorem of this section

HomFOUnique :  {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} {f g : A → B} (homf : HomFO f) (homg : HomFO g) → f ≡ g

HomFOUnique {f = f} {g = g}  homf homg = isoCancel (isoPostComp isIsoFO)
                                        (isoCancel (isoPreComp (isoInv isIsoFO))
                                                   (HomFOUniqueCanonical (HomFOComp (HomFOComp HomFOcanonicalInv homf) HomFOcanonical)
                                                                         (HomFOComp (HomFOComp HomFOcanonicalInv homg) HomFOcanonical)))
