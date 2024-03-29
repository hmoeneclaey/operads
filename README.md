# Formalising ∞-Monoids in Two-Level Type Theory 

This repository contains a definition of ∞-monoids using operads, with a proof that they are invariant by equivalences and that loop spaces are such monoids.


## Organisation

To type-check this project, it is enough to load `MainTheorem.agda`, this takes ~5min on my computer. It does not use any standard library, except `Agda.Primitive.agda` for universe levels.


## Complete Files

- `Data.agda` : very basic things, with function extensionality for strict equality postulated.

About operads:

- `FiniteSet.agda` : defines finite sets.
- `MorphismFiniteSet.agda` : defines the morphisms of finite sets necessary for the definition of operad.
- `FiniteSet2.agda` : more on finite sets, necessary for `LoopSpace.agda`.
- `Operad.agda` : defines operads.
- `LimitOperad.agda` : postulates pullback of operads, can be proven easily but long to typecheck.
- `OperadCocyl.agda` : defines the cocylinder factorisation for operads.

About the homotopy structure:

- `FibrantUniverse.agda` : postulates the homotopy structure on universes.
- `Cofibration.agda` : defines cofibrations and pseudo-cofibrations.
- `LoopSpace.agda` : defines the PathSpace operad, and shows it is strongly contractible.

Linking operads with the homotopy structure:

- `CofibrantOperad.agda` : defines cofibrant operads by LLP against trivial fibrations, shows they have LLP against equivalences between fibrant operads.
- `HomotopyTransfer.agda` : shows algebras for cofibrant operads invariant under equivalences.
- `ContractibleSectionOperad.agda` : shows an operad with sections against strongly contractible morphism is cofibrant and acts on loop spaces.
- `MainTheorem.agda` : main result.



## Incomplete Files

In 'MainTheorem.agda', an operad ∞Mon that has sections against strongly contractible morphisms is postulated. The following incomplete files aim to construct it using labelled trees:

- `AltOperad.agda`
- `LabelledTree.agda`
- `RewritingLabelledTree.agda` 
- `QuotientLabelledTree.agda`
- `FiltrationLabelledTree.agda`

