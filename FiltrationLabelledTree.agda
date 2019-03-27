{-# OPTIONS --rewriting #-}

module FiltrationLabelledTree where


open import Data
open import LabelledTree
open import FiniteSet
open import RewritingLabelledTree
open import QuotientLabelledTree
open import AltOperad
open import FibrantUniverse
open import Cofibration



--First some things about ≤ on ℕ

ordℕ : ℕ → ℕ → Set
ordℕ m n = {!!}

_⊂_ : ℕ → ℕ → Set
m ⊂ n = (m ≡ n) ∨ ordℕ m n

Prop⊂ : {m n : ℕ} → isProp (m ⊂ n)
Prop⊂ = {!!}

⊂O : {n : ℕ} → O ⊂ n
⊂O = {!!}

O⊂ : {n : ℕ} → n ⊂ O → n ≡ O
O⊂ = {!!}

⊂s : {m n : ℕ} → m ⊂ n → s m ⊂ s n
⊂s = {!!}

¬⊂ : {n : ℕ} → ¬ (s n ⊂ n)
¬⊂ = {!!}

⊂Trans : {m n l : ℕ} → m ⊂ n → n ⊂ l → m ⊂ l
⊂Trans = {!!}

NumberSum : {m n : ℕ} → Σ ℕ (λ k → m ≡ k + n) ∨ Σ ℕ (λ k → k + m ≡ n)
NumberSum = {!!}

⊂finiteSum : {n : ℕ} {S : Fin n → ℕ} (a : Fin n) → S a ⊂ finiteSum S
⊂finiteSum = {!!}



--We define trees with at most k internal vertices

record ≤Ltree (k : ℕ) (n : ℕ) : Set where
  field
    tree : Ltree n
    size : cardinalInternalVertice tree ⊂ k

≡≤Ltree : {k n : ℕ} → {t₁ t₂ : ≤Ltree k n} → ≤Ltree.tree t₁ ≡ ≤Ltree.tree t₂ → t₁ ≡ t₂
≡≤Ltree {t₁ = record { tree = t₁ ; size = _ }}
        {record { tree = t₂ ; size = _ }} refl
      = ap (λ eq → record { tree = t₁ ; size = eq }) Prop⊂


incLtree : {k n : ℕ} → ≤Ltree (pred k) n → ≤Ltree k n
incLtree record { tree = t ; size = eq } = record { tree = t ; size = {!!} }

LtreeTo≤Ltree : {n : ℕ} (t : Ltree n) → ≤Ltree (cardinalInternalVertice t) n
LtreeTo≤Ltree t = record { tree = t ; size = left refl }

≤LtreeToLtree : {k n : ℕ} (t : ≤Ltree k n) → Ltree n
≤LtreeToLtree = ≤Ltree.tree


data _⇒₂_ : {k n : ℕ} → ≤Ltree k n → ≤Ltree (pred k) n → Set where
  mk⇒₂ : {n : ℕ} {t₁ t₂ : Ltree n} → t₁ ⇒ t₂ → LtreeTo≤Ltree t₁ ⇒₂ record { tree = t₂ ; size = {!!} }


⊥Ltree₂ : {k n : ℕ} → (t : ≤Ltree k n) (a : InternalVertice (≤LtreeToLtree t)) → ≤Ltree (pred k) (cardinal⊥Ltree a)
⊥Ltree₂ record { tree = t ; size = _ } a = record { tree = ⊥Ltree a ; size = {!!} }

⊤Ltree₂ : {k n : ℕ} → (t : ≤Ltree k n) (a : InternalVertice (≤LtreeToLtree t)) → ≤Ltree (pred k) (cardinal⊤Ltree a)
⊤Ltree₂ record { tree = t ; size = _ } a = record { tree = ⊤Ltree a ; size = {!!} }



--Some properties of small Ltree

≤LtreeOProp : {n : ℕ} → Ltree  n → Set
≤LtreeOProp {O} t = t ≡ μ
≤LtreeOProp {s O} t = (t ≡ μ) ∨ (t ≡ ∅)
≤LtreeOProp {s (s n)} t = t ≡ μ

≤LtreeAux₁ : {n : ℕ} → ≤LtreeOProp (μ {n})
≤LtreeAux₁ {O} = refl
≤LtreeAux₁ {s O} = left refl
≤LtreeAux₁ {s (s n)} = refl

≤LtreeAux₂ : {n : ℕ} {S : Fin n → ℕ} {t : (k : Fin n) → Ltree+ (S k)}
             → ((k : Fin n) → cardinalInternalVertice+ (t k) ≡ O)
             → μ ≡ cons t
≤LtreeAux₂ = {!!}

≤LtreeO : {n : ℕ} {t : ≤Ltree O n} → ≤LtreeOProp (≤LtreeToLtree t)
≤LtreeO {.(s O)} {record { tree = ∅ ; size = _ }} = right refl
≤LtreeO {.(finiteSum S)} {record { tree = cons {S = S} x ; size = size }} = transport ≤LtreeOProp {x = μ}
                                                                                      (≤LtreeAux₂ λ k → O⊂ (⊂Trans (⊂finiteSum k) size))
                                                                                      ≤LtreeAux₁

{-
≤LtreeO : {t : ≤Ltree O O} → ≤LtreeToLtree t ≡ μ
≤LtreeO {t = t} = {!!}


≤LtreeOS : {t : ≤Ltree O (s O)} → (≤LtreeToLtree t ≡ μ) ∨ (≤LtreeToLtree t ≡ ∅)
≤LtreeOS = {!!}

≤LtreeOSS : {n : ℕ} {t : ≤Ltree O (s (s n))} → ≤LtreeToLtree t ≡ μ
≤LtreeOSS = {!!}
-}

≤LtreeVertice+ : {n : ℕ} {t : Ltree+ n} → InternalVertice+ t → s O ⊂ cardinalInternalVertice+ t 
≤LtreeVertice+ {t = ∅+} () 
≤LtreeVertice+ {t = cons+ _ x} _ = ⊂s ⊂O


≤LtreeVertice : {n : ℕ} {t : Ltree n} → InternalVertice t → s O ⊂ cardinalInternalVertice t 
≤LtreeVertice {t = ∅} () 
≤LtreeVertice {t = cons x} (mkInternalVerice .x a b) = ⊂Trans {n = cardinalInternalVertice+ (x a)}
                                                              (≤LtreeVertice+ b)
                                                              (⊂finiteSum a)

≤LtreeONoVertice : ∀ {k} {X : Set k} {n : ℕ} {t : ≤Ltree O n} → InternalVertice (≤LtreeToLtree t) → X
≤LtreeONoVertice {t = t} a = efql (¬⊂ (⊂Trans (≤LtreeVertice a) (≤Ltree.size t)))


--An auxiliary property

module _ {u} {v} {P : ℕ → Set u} {Q : ℕ → Set v} {{_ : AltOperad P}} {{_ : AltOperad Q}}
         {β : {n : ℕ} → P n → Q n} where

       transportOperad : {m m' n n' : ℕ} {p : m ≡ m'} {q : n ≡ n'} {r : pred (m' + n') ≡ pred (m + n)}
                         {c : P m} {d : P n} {k : Fin m}
                         → transport Q r (γAlt (β (transport P p c)) (transport Fin p k) (β (transport P q d))) ≡ γAlt (β c) k (β d) 
       transportOperad {p = refl} {refl} {refl} = refl


--Morphism build using filtration

module _ {k} {P : ℕ → Set k} {{_ : AltOperad P}}
         (α : {k n : ℕ} → ≤Ltree k n → P n)
         (αinc : {k n : ℕ} → {t : ≤Ltree (pred k) n} → α t ≡ α {k} (incLtree t))
         where

       ≡αLtreeAux : {k l n : ℕ} {t₁ : ≤Ltree l n} {t₂ : ≤Ltree (k + l) n}
                    → ≤LtreeToLtree t₁ ≡ ≤LtreeToLtree t₂ → α t₁ ≡ α t₂
       ≡αLtreeAux {O} eq = ap α (≡≤Ltree eq)
       ≡αLtreeAux {s k} {l} {t₁ = t₁} {t₂} eq = ≡Trans {y = α (incLtree {s l} t₁)}
                                                       (αinc {s l})
                                                       (≡αLtreeAux {k} {s l} eq)

       ≡αLtree : {n k₁ k₂ : ℕ} {t₁ : ≤Ltree k₁ n} {t₂ : ≤Ltree k₂ n}
                 → ≤LtreeToLtree t₁ ≡ ≤LtreeToLtree t₂ → α t₁ ≡ α t₂ 
       ≡αLtree {_} {k₁} {k₂} = ∨Elim (λ { (_ , refl) eq → ≡Sym (≡αLtreeAux (≡Sym eq))})
                                     (λ { (_ , refl) eq → ≡αLtreeAux eq})
                                     (NumberSum {k₁} {k₂})

       MapFiltrationAux : {n : ℕ} → Ltree n → P n
       MapFiltrationAux = α o LtreeTo≤Ltree

       module _ (αid : α (LtreeTo≤Ltree idLtree) ≡ idAlt)
                (αγ : {k n : ℕ} {t : ≤Ltree k n} (a : InternalVertice (≤LtreeToLtree t)) → EvalLtree a ≡ e₁
                → α t ≡ transport P (≡cardinal⊥⊤Ltree {k = a}) (γAlt (α (⊥Ltree₂ t a)) (leaf⊥Ltree a) (α (⊤Ltree₂ t a)))) where

              HomAltOpFiltrationAux : HomAltOperad {{OpLtree}} MapFiltrationAux
              HomAltOpFiltrationAux = record { HomIdAlt = αid ;
                                               HomγAlt = λ t₁ {k} t₂ → let H = Internalγ t₁ k t₂ in
                                                         ≡Trans (αγ (Internalγ t₁ k t₂) Internalγe₁)
                                                                (≡Trans {y = transport P ≡cardinal⊥⊤Ltree
                                                                        (γAlt (α (LtreeTo≤Ltree (⊥Ltree (Internalγ t₁ k t₂))))
                                                                              (leaf⊥Ltree (Internalγ t₁ k t₂))
                                                                              (α (LtreeTo≤Ltree (⊤Ltree (Internalγ t₁ k t₂)))))}
                                                                        (ap (transport P ≡cardinal⊥⊤Ltree)
                                                                            (ap₂ (λ x y → γAlt x (leaf⊥Ltree (Internalγ t₁ k t₂)) y)
                                                                                 {a₁ = α (⊥Ltree₂ (LtreeTo≤Ltree (γLtree t₁ k t₂)) (Internalγ t₁ k t₂))}
                                                                                 {a₂ = α (LtreeTo≤Ltree (⊥Ltree (Internalγ t₁ k t₂)))}
                                                                                 {b₁ = α (⊤Ltree₂ (LtreeTo≤Ltree (γLtree t₁ k t₂)) (Internalγ t₁ k t₂))}
                                                                                 {b₂ = α (LtreeTo≤Ltree (⊤Ltree (Internalγ t₁ k t₂)))}
                                                                        (≡αLtree refl)
                                                                        (≡αLtree refl)))
                                                                (≡Trans {y = transport P (≡cardinal⊥⊤Ltree {k = Internalγ t₁ k t₂})
                                                                        (γAlt {m = cardinal⊥Ltree H} {n = cardinal⊤Ltree H}
                                                                              (MapFiltrationAux (transport Ltree ≡Internalγ⊥ t₁))
                                                                              (transport Fin ≡Internalγ⊥ k)
                                                                              (MapFiltrationAux (transport Ltree ≡Internalγ⊤ t₂)))}
                                                                        (ap (transport P ≡cardinal⊥⊤Ltree)
                                                                            (≡Trans (ap₂ (λ x y → γAlt x (leaf⊥Ltree (Internalγ t₁ k t₂)) y)
                                                                                         {a₁ = α (LtreeTo≤Ltree (⊥Ltree (Internalγ t₁ k t₂)))}
                                                                                         {a₂ = MapFiltrationAux (transport Ltree ≡Internalγ⊥ t₁)}
                                                                                         {b₁ = α (LtreeTo≤Ltree (⊤Ltree (Internalγ t₁ k t₂)))}
                                                                                         {b₂ = MapFiltrationAux (transport Ltree ≡Internalγ⊤ t₂)}
                                                                                     (ap MapFiltrationAux ≡Internalγ⊥Ltree)
                                                                                     (ap MapFiltrationAux ≡Internalγ⊤Ltree))
                                                                                     (ap (λ k₁ → γAlt (MapFiltrationAux (transport Ltree ≡Internalγ⊥ t₁)) k₁
                                                                                                      (MapFiltrationAux (transport Ltree ≡Internalγ⊤ t₂)))
                                                                                          ≡leaf⊤Ltree)))
                                                                        (transportOperad {β = MapFiltrationAux})) ) }
       
              module _  (α⇒ : {k n : ℕ} {t₁ : ≤Ltree k n} {t₂ : ≤Ltree (pred k) n} → t₁ ⇒₂ t₂ → α t₁ ≡ α t₂) where
       
                MapFiltration : {n : ℕ} → Qtree n → P n 
                MapFiltration = QtreeRec MapFiltrationAux (λ r → ≡Trans (α⇒ (mk⇒₂ r)) (≡αLtree refl))

                HomAltOpFiltration : HomAltOperad {{OpQtree}} MapFiltration
                HomAltOpFiltration = QtreeRecOperad HomAltOpFiltrationAux

                module _ {β : {n : ℕ} → P n → Qtree n}
                         (αsec : {k n : ℕ} {t : ≤Ltree k n} → β (α t) ≡ [ ≤LtreeToLtree t ]) where

                       SectionFiltration : {n : ℕ} (t : Qtree n) → β (MapFiltration t) ≡ t
                       SectionFiltration = QtreeProp (λ _ → αsec) UIP




--We conclude that Qtree has sections against strongly contractible morphism

module _ {l} {P : ℕ → Set l} {{opP : AltOperad P}}
         {β : {n : ℕ} → P n → Qtree n}
         {homβ : HomAltOperad {{opP}} {{OpQtree}} β}
         (contrβ : {n : ℕ} → StronglyContractibleMap (β {n})) where

       record Partial (k : ℕ) : Set l where
         field
           morphism : {n : ℕ} → ≤Ltree k n → P n
           section : {n : ℕ} {t : ≤Ltree k n} → β (morphism t) ≡ [ ≤LtreeToLtree t ]
           reduction : {n : ℕ} {t₁ : ≤Ltree k n} {t₂ : ≤Ltree (pred k) n} → t₁ ⇒₂ t₂ → morphism t₁ ≡ morphism (incLtree t₂)
           composition : {n : ℕ} {t : ≤Ltree k n} (a : InternalVertice (≤LtreeToLtree t)) → EvalLtree a ≡ e₁
                         → morphism t ≡ transport P (≡cardinal⊥⊤Ltree {k = a})
                                        (γAlt (morphism (incLtree (⊥Ltree₂ t a))) (leaf⊥Ltree a) (morphism (incLtree (⊤Ltree₂ t a))))
                                      

       --We prove that there is a O-morphism

       secβ : {n : ℕ} → fibre β ([ μ {n} ])
       secβ = SectionStronglyContractibleMap contrβ [ μ ]

       PartialOMap : {n : ℕ} → ≤Ltree O n → P n
       PartialOMap {O} _ = fibre.point secβ
       PartialOMap {s O} _ = idAlt
       PartialOMap {s (s n)} _ = fibre.point secβ 

       PartialO : Partial O
       PartialO = record
                    { morphism = PartialOMap ;
                      section = λ { {O} {t} → ≡Trans (fibre.equal secβ)
                                                     (ap [_] (≡Sym (≤LtreeO {t = t}))) ;
                                    {s O} {t} → ≡Trans (HomAltOperad.HomIdAlt homβ)
                                                       (∨Elim (λ eq → ≡Trans (≡Sym (Qtree⇒ μ∅⇒)) (ap [_] (≡Sym eq)))
                                                              (λ eq → ap [_] (≡Sym eq))
                                                              (≤LtreeO {t = t})) ;
                                    {s (s n)} {t} → ≡Trans (fibre.equal secβ)
                                                           (ap [_] (≡Sym (≤LtreeO {t = t})))} ; 
                      reduction = λ _ → refl ;
                      composition = λ {_} {t} a → ≤LtreeONoVertice {t = t} a }


       --We prove that k-morphism can be extended to (k + 1)-morphism
       
       extend : {k : ℕ} → Partial k → Partial (s k)
       extend = {!!}
        
       extendInc : {k n : ℕ} {p : Partial k} {t : ≤Ltree k n} → Partial.morphism p t ≡ Partial.morphism (extend p) (incLtree t)
       extendInc = {!!}


       --We conclude that Qtree has strongly contractible sections

       PartialAux : (k : ℕ) → Partial k
       PartialAux O = PartialO
       PartialAux (s k) = extend (PartialAux k)

       α : {k n : ℕ} → ≤Ltree k n → P n
       α {k} = Partial.morphism (PartialAux k)

       αinc : {k n : ℕ} {t : ≤Ltree (pred k) n} → α t ≡ α {k} (incLtree t)
       αinc {O} {t = t} = ap (α {O}) {x = t} {y = incLtree t} (≡≤Ltree refl) 
       αinc {s k} = extendInc {p = PartialAux k}

       αid : α (LtreeTo≤Ltree idLtree) ≡ idAlt
       αid = refl

       αγ : {k n : ℕ} {t : ≤Ltree k n} (a : InternalVertice (≤LtreeToLtree t)) → EvalLtree a ≡ e₁
                → α t ≡ transport P (≡cardinal⊥⊤Ltree {k = a}) (γAlt (α (⊥Ltree₂ t a)) (leaf⊥Ltree a) (α (⊤Ltree₂ t a)))
       αγ {k} {t = t} a eq = ≡Trans (Partial.composition (PartialAux k) {t = t} a eq)
                                     (ap (transport P ≡cardinal⊥⊤Ltree) (ap₂ (λ b₁ b₂ → γAlt b₁ (leaf⊥Ltree a) b₂)
                                                                           {a₁ = α {k} (incLtree (⊥Ltree₂ t a))} {a₂ = α (⊥Ltree₂ t a)}
                                                                           {b₁ = α {k} (incLtree (⊤Ltree₂ t a))} {b₂ = α (⊤Ltree₂ t a)}
                                                                           (≡Sym (αinc {k}))
                                                                           (≡Sym (αinc {k}))))

       MapFiltrationPartialAux : {n : ℕ} → Ltree n → P n
       MapFiltrationPartialAux = MapFiltrationAux α (λ {k} → αinc {k})

       HomOpPartialAux : HomAltOperad {{OpLtree}} MapFiltrationPartialAux
       HomOpPartialAux = HomAltOpFiltrationAux α (λ {k} → αinc {k}) αid (λ {k} → αγ {k})
        
       α⇒ : {k n : ℕ} {t₁ : ≤Ltree k n} {t₂ : ≤Ltree (pred k) n} → t₁ ⇒₂ t₂ → α t₁ ≡ α t₂
       α⇒ {k} r = ≡Trans (Partial.reduction (PartialAux k) r) (≡Sym (αinc {k}))

       αsec : {k n : ℕ} {t : ≤Ltree k n} → β (α t) ≡ [ ≤LtreeToLtree t ]
       αsec {k} = Partial.section (PartialAux k)

       MapFiltrationPartial : {n : ℕ} → Qtree n → P n
       MapFiltrationPartial = MapFiltration α (λ {k} → αinc {k}) αid (λ {k} → αγ {k}) α⇒ 

       SectionMapFiltration : {n : ℕ} {t : Qtree n} → β (MapFiltrationPartial t) ≡ t
       SectionMapFiltration {t = t} = SectionFiltration α (λ {k} → αinc {k}) αid (λ {k} → αγ {k}) α⇒ {β = β} (λ {k} → αsec {k}) t



