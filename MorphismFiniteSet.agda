module MorphismFiniteSet where

open import Data
open import FiniteSet


--Morphisms between FOSet
isOrderPreserving : {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} (f : A → B) → Set
isOrderPreserving {A} f = (x y : A) → x << y ↔ f x << f y


record HomFO {A B : Set} {{Afinite : FOSet A}} {{Bfinite : FOSet B}} (f : A → B) : Set where
  field
    isoHomFO : iso f
    orderPreserving : isOrderPreserving f

--open HomFO {{...}} public





--We construct some basic instance of FOSet

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



--We construct the isomorphism needed for the definition of operads

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







--We show that being a morphism of FOSet is a property

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




--Some properties of morphism between canonical finite sets

postulate
  IsoCardinal : {m n : ℕ} {f : Fin m → Fin n} → iso f → n ≡ m

postulate
  surjectiveInjective : {m : ℕ} → {f : Fin m → Fin m} → injective f → surjective f




--We show some properties of order preserving functions



--fsuccOrderPreserving : {m : ℕ} → isOrderPreserving (fsucc {m})
--fsuccOrderPreserving _ _ = ↔Refl

injectiveOrderPreserving : {m : ℕ} {f : Fin m → Fin m} → isOrderPreserving f → injective f
injectiveOrderPreserving ordf {x = x} {y = y} p = <Total (λ ordxy → <IreflEqual p (∧left (ordf x y) ordxy))
                                                          λ ordyx → <IreflEqual (≡Sym p) (∧left (ordf y x) ordyx)

surjectiveOrderPreserving : {m : ℕ} {f : Fin m → Fin m} → isOrderPreserving f → surjective f
surjectiveOrderPreserving ordf = surjectiveInjective (injectiveOrderPreserving ordf) 


orderFzero : {m : ℕ} (f : Fin (s m) → Fin (s m)) → isOrderPreserving f → f fzero ≡ fzero

orderFzero f ordf = isFzero (λ y ordy → let a = Σleft (surjectiveOrderPreserving {f = f} ordf y) in
                                        let eqa : f a ≡ y
                                            eqa = Σright (surjectiveOrderPreserving {f = f} ordf y) in
                                        let orda : f a << f fzero
                                            orda = transport (λ x₁ → x₁ << f fzero) (≡Sym eqa) ordy in 
                                        <MinFzero {n = a} (∧right (ordf _ _) orda))


HomFOfunction : {m : ℕ} (f : Fin (s m) → Fin (s m)) → isOrderPreserving f → Fin m → Fin m
HomFOfunction f ordf x = Σleft (isSucc {x = f (fsucc x)} (transport (λ y → y << f (fsucc x)) (orderFzero f ordf)
                                                                    (∧left (ordf fzero (fsucc x)) *))) 


HomFOUniqueAux1 : {m : ℕ} (f : Fin (s m) → Fin (s m)) (ordf : isOrderPreserving f)
                  → {a : Fin m} → f (fsucc a) ≡ fsucc (HomFOfunction f ordf a)
HomFOUniqueAux1 f ordf {x} = Σright (isSucc {x = f (fsucc x)} (transport (λ y → y << f (fsucc x)) (orderFzero f ordf)
                                                                         (∧left (ordf fzero (fsucc x)) *))) 


HomFOUniqueAux : {m : ℕ} {f : Fin m → Fin m} → isOrderPreserving f → f ≡ Id

HomFOUniqueAux {O} {f = f} Hyp = funext (λ ()) 

HomFOUniqueAux {s n} {f = f} ordf = funext (λ { fzero → orderFzero f ordf ;
                                                (fsucc a) → let g = HomFOfunction f ordf in
                                                            ≡Trans {y = fsucc (g a)}
                                                                   (HomFOUniqueAux1 f ordf)
                                                                   (ap fsucc (≡fun (HomFOUniqueAux {f = g} λ x y →
                                                                             (↔Trans (f (fsucc x) << f (fsucc y))
                                                                                     (ordf _ _)
                                                                                     (transport₂↔ _<<_ {a₁ = f (fsucc x)}
                                                                                                               {a₂ = fsucc (g x)}
                                                                                                               {b₁ = f (fsucc y)}
                                                                                                               {b₂ = fsucc (g y)}
                                                                                                        (HomFOUniqueAux1 f ordf)
                                                                                                        (HomFOUniqueAux1 f ordf))))))})



--We show that morphisms between FOSet are unique


orderPreservingTransport : {m n : ℕ} (p : m ≡ n) {x y : Fin m} → x << y ↔ transport Fin p x << transport Fin p y
orderPreservingTransport refl = ↔Refl


HomFOUniqueCanonical : {m n : ℕ} {f g : Fin m → Fin n} (homf : HomFO f) (homg : HomFO g) → f ≡ g

HomFOUniqueCanonical {f = f} {g = g} homf homg = let p = IsoCardinal (HomFO.isoHomFO homf) in
                                                 isoCancel (isoPostComp (isoTransport Fin p))
                                                   (≡Trans {y = Id}
                                                           (HomFOUniqueAux λ x y → ↔Trans (f x << f y)
                                                                                          (HomFO.orderPreserving homf x y)
                                                                                          (orderPreservingTransport p))
                                                     (≡Sym (HomFOUniqueAux (λ x y → ↔Trans (g x << g y)
                                                                                           (HomFO.orderPreserving homg x y)
                                                                                           (orderPreservingTransport p)))))


HomFOUnique :  {A B : Set} {{_ : FOSet A}} {{_ : FOSet B}} {f g : A → B} (homf : HomFO f) (homg : HomFO g) → f ≡ g

HomFOUnique {f = f} {g = g}  homf homg = isoCancel (isoPostComp isIsoFO)
                                        (isoCancel (isoPreComp (isoInv isIsoFO))
                                                   (HomFOUniqueCanonical (HomFOComp (HomFOComp HomFOcanonicalInv homf) HomFOcanonical)
                                                                         (HomFOComp (HomFOComp HomFOcanonicalInv homg) HomFOcanonical)))
