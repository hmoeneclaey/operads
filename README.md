# Formalising ∞-Monoids in Two-Level Type Theory 


## Data.agda

Contains logical connectives, natural numbers, equality and isomorphisms, along with some basic properties.


## FiniteSet.agda

Contains a definition of (small) finite totally ordered sets as types isomorphic to a canonical finite type.

Main results :

     - The finite union of finite sets is finite

     - Explicit description of the order on these unions

     - Some morphisms of finite totally ordered sets


## Operad.agda

Contains the definition of ns-operads and their algebras.


## FibrantUniverses.agda

Contains the definition of the fibrant structure. This is where almost all our postulates are (except strict function extesionnality).

It contains basic definition of HoTT and

   - Fibrations
   
   - Trivial Fibrations

   - Cofibrancy of finite sets

I am thinking about separating HoTT results from the rest.


## CofibrantOperads.agda

Contains the definition of cofibrant operads (as left lifting property against trivial fibrations), and shows that they have the left lifting property against equivalences between fibrant operads.

## OperadCocylinder.agda

Auxiliary file for CofibrantOperads.agda, it takes ~2 min to typecheck.

## HomotopyTransfer.agda

Contains a proof that fibrant algebras for cofibrant operads are invariant by equivalence.