# Formalising ∞-Monoids in Two-Level Type Theory 


## Data.agda

Contains logical connectives, natural numbers, equality and isomorphisms, along with some basic properties.


## FiniteSet.agda

Contains a definition of (small) finite totally ordered sets as types isomorphic to a canonical finite type.

Main results :

     - The finite union of finite sets is finite

     - Explicit description of the order on these unions


## MorphismFiniteSet.agda

Contains a definition of isomorphism between finite totally ordered sets, along with

	 - the example of morphism needed for the definition of operads

	 - a proof that there exists at most one isomorphism between two finite totally ordered sets.


## Operad.agda

Contains the definition of operads and their algebras.


## FibrantUniverse.agda

Contains the definition of the fibrant structure. This is where almost all our postulates are (except strict function extensionnality).

It contains basic definition of HoTT and

      - definition of Fibrations and Trivial Fibrations

      - Cofibrancy of finite sets


## CofibrantOperad.agda

Contains the homotopical structure on operads, notably :

	 - definition of fibrant and cofibrant operads, of fibration, trivial fibration and equivalences of operads.

	 - Prove cofibrant operads have a weak left lifting property against equivalences between fibrant operads.


## OperadCocylinder.agda

Auxiliary file for CofibrantOperad.agda, it takes ~2 min to typecheck.


## HomotopyTransfer.agda

Contains a proof that fibrant algebras for cofibrant operads are invariant under equivalence.


## Cofibration.agda

Contains the definitions of cofibration and pseudo-cofibration, together with a proof that the inclusion of its border in a cube is a cofibration and pseudo-cofibration.