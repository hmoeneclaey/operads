# Formalising ∞-Monoids in Two-Level Type Theory 

This repository contains a formalisation of ∞-monoids in a two-level type theory, with a proof that they are invariant by equivalence and that loop spaces are such monoids.

## Complete Files

- 'Data.agda' : logical connectives, natural numbers, equality and basic properties

Things about operads, without using the homotopy structure:

- 'FiniteSet.agda' : define finite sets.
- 'MorphismFiniteSet.agda' : define morphisms necessary for the definition of operad.
- 'FiniteSet2.agda' : more on finite set, necessary for 'LoopSpace.agda'.
- 'Operad.agda' : define operad.
- 'LimitOperad.agda' : postulate pullback of operad. Can be proven easily but long to typecheck.
- 'OperadCocyl.agda' : the cocylinder factorisation for operad.

About the homotopy structure:

- 'FibrantUniverse.agda' : postulate the homotopy structure.
- 'Cofibration.agda' : define cofibrations and pseudo-cofibrations.
- 'LoopSpace.agda' : define the PathSpace operad, and show it is strongly contractible.

Linking operads with the homotopy structure:

- 'CofibrantOperad.agda' : define cofibrant operads by LLP against trivial fibrations, show they have LLP against equivalences between fibrant operads.
- 'HomotopyTransfer.agda' : show fibrant algebras for cofibrant operads invariant under equivalence.
- 'ContractibleSectionOperad.agda' : shows an operad with section against strongly contractible morphism is cofibrant and acts on loop spaces.
- 'MainTheorem.agda' : main result.



## Incomplete Files

In 'MainTheorem.agda', the operad ∞Mon is potulated with its property. The following files are incomplete and aim to complete this hole:

- 'AltOperad'
- 'LabelledTree'
- 'RewritingLabelledTree.agda' 
- 'QuotientLabelledTree.agda'
- 'FiltrationLabelledTree.agda'

