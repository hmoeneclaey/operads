# Formalising ∞-Monoids in Two-Level Type Theory 

This repository contains a definition of ∞-monoids using operads, with a proof that they are invariant by equivalence and that loop spaces are such monoids. We do not use any library (except `Agda.Primive.agda` for levels in the universe).


## Complete Files

- `Data.agda` : very basic things, with function extensionality for strict equality postulated.

About operads:

- `FiniteSet.agda` : define finite sets.
- `MorphismFiniteSet.agda` : define morphisms of finite sets necessary for the definition of operad.
- `FiniteSet2.agda` : more on finite set, necessary for `LoopSpace.agda`.
- `Operad.agda` : define operad.
- `LimitOperad.agda` : postulate pullback of operad, can be proven easily but long to typecheck.
- `OperadCocyl.agda` : the cocylinder factorisation for operad.

About the homotopy structure:

- `FibrantUniverse.agda` : postulate the homotopy structure.
- `Cofibration.agda` : define cofibrations and pseudo-cofibrations.
- `LoopSpace.agda` : define the PathSpace operad, and show it is strongly contractible.

Linking operads with the homotopy structure:

- `CofibrantOperad.agda` : define cofibrant operads by LLP against trivial fibrations, show they have LLP against equivalences between fibrant operads.
- `HomotopyTransfer.agda` : show fibrant algebras for cofibrant operads invariant under equivalence.
- `ContractibleSectionOperad.agda` : shows an operad with section against strongly contractible morphism is cofibrant and acts on loop spaces.
- `MainTheorem.agda` : main result.



## Incomplete Files

In 'MainTheorem.agda', an operad ∞Mon that has section against strongly contractible morphisms is postulated. The following incomplete files aim to contruct it using labelled trees:

- `AltOperad.agda`
- `LabelledTree.agda`
- `RewritingLabelledTree.agda` 
- `QuotientLabelledTree.agda`
- `FiltrationLabelledTree.agda`

