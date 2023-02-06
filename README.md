Presentation
=======

This repo contains formalisation work on implementing a logical relation over MLTT with one universe.
This formalisation follows the [work done by Abel et al.]((https://github.com/mr-ohman/logrel-mltt/)) (described in [Decidability of conversion for Type Theory in Type Theory, 2018](https://dl.acm.org/doi/10.1145/3158111)), and [Loïc Pujet's work](https://github.com/loic-p/logrel-mltt) on removing induction-recursion from the previous formalization, making it feasible to translate it from Agda to Coq.

The definition of the logical relation (**LR**) ressembles Loïc's in many ways, but also had to be modified for a few reasons :
- Because of universe constraints and the fact that functors cannot be indexed by terms in Coq whereas it is possible in Agda, the relevant structures had to be parametrized by a type level and a recursor, and the module system had to be dropped out entirely.
- Since Coq and Agda's positivity checking for inductive types is different, it turns out that **LR**'s definition, even though it does not use any induction-induction or induction-recursion in Agda, is not accepted in Coq. As such, the predicate over Π-types for **LR** has been modified compared to Agda. You can find a MWE of the difference in positivity checking in the two systems in [Positivity.v] and [Positivity.agda].

In order to avoid some work on the syntax, this project uses the [Autosubst](https://github.com/uds-psl/autosubst-ocaml) project to generate syntax-related boilerplate.

Building
===========

The project builds with Coq version `8.15.2`. Once Coq has been installed, you can simply issue `make` in the root folder.


File description
==========

Utilities and AST
---------

| File | Description |
|---|----|
[Utils] | Basic generically useful definitions, notations, tactics…
[BasicAst] | Definitions preceding the definition of the AST itself: sorts, binder annotations…
[AutoSubst/] | Abstract syntax tree, renamings, substitutions and many lemmas, generated using the [autosubst-ocaml] opam package.
[Notations] | Notations used throughout the file. It can be used as an index for notations!
[Untyped] | Various useful definitions for defining the inference rules |

Common typing-related definitions
-------

| File | Description |
|---|----|
[Context] | Context-related definitions: declaration, mapping over a context, find a type in a context…
[UntypedReduction] | Definiton and basic properties of untyped reduction, used to define algorithmic typing.
[Weakening] | Definition of a well-formed weakening, and some properties.
[GenericTyping] | A generic notion of typing, used to define the logical relation, to be instantiated twice: once with the declarative version, and once with the algorithmic one.

Declarative typing and its properties
--------------

| File | Description |
|---|----|
[DeclarativeTyping] | Defines the theory's typing rules in a declarative fashion, the current definition has a single universe as well as product types and eta-conversion for functions. |
[Generation] | Contains generation theorems, giving a good inversion on term typing/reduction with a direct structural premise
[Reduction] | Basic properties of reduction, enough to derive that declarative typing is an instance of generic typing. |

Logical relation and its properties
-----------

| File | Description |
|---|----|
[LogicalRelation] | Contains the logical relation's (**LR**) definition. |
| [LRInduction] | Defines the induction principles over **LR**. Because of universe constraints, **LR** needs two induction principles, one for each type levels. |
| [Escape] | Contains a proof of the escape lemma for **LR** |
| [Shapeview] | Technique to avoid considering non-diagonal cases for two reducibly convertible types. |
[Reflexivity] | Reflexivity of the logical relation.
[Irrelevance] | Irrelevance of the logical relation: two convertible types decode to equivalent predicates. Symmetry is a direct corollary. |

Algorithmic typing and its properties
-----------------

| File | Description |
|---|----|
[AlgorithmicTyping] | Definition of the second notion of typing : algorithmic typing (and algorithmic conversion together with it).
[LogRelConsequences] | Consequences of the logical relation on declarative typing necessary to establish properties of algorithmic typing.
[BundledAlgorithmicTyping] | Algorithmic typing bundled with its pre-conditions, and a tailored induction principle showing invariant preservation in the "algorithm".
[AlgorithmicTypingProperties] | Properties of algorithmic typing, in order to derive the second instance of generic typing. |

Miscellaneous
-----------

| File | Description |
|---|----|
| [Positivity.v] and [Positivity.agda] | Showcase the difference between Coq and Agda's positivity checkers. |

[Utils]: ./theories/Utils.v
[BasicAst]: ./theories/BasicAst.v
[Context]: ./theories/Context.v
[AutoSubst/]: ./theories/Autosubst/
[Notations]: ./theories/Notations.v
[Automation]: ./theories/Automation.v
[Untyped]: ./theories/Untyped.v
[UntypedReduction]: ./theories/UntypedReduction.v
[GenericTyping]: ./theories/GenericTyping.v
[DeclarativeTyping]: ./theories/DeclarativeTyping.v
[Properties]: ./theories/Properties.v
[Reduction]: ./theories/Reduction.v
[Generation]: ./theories/Generation.v
[LogicalRelation]: ./theories/LogicalRelation.v
[LRInduction]: ./theories/LRInduction.v
[Escape]: ./theories/Escape.v
[Reflexivity]: ./theories/Reflexivity.v
[Irrelevance]: ./theories/Irrelevance.v
[ShapeView]: ./theories/ShapeView.v
[Positivity.v]: ./theories/Positivity.v
[Weakening]: ./theories/Weakening.v
[Substitution]: ./theories/Substitution.v
[AlgorithmicTyping]: ./theories/AlgorithmicTyping.v
[AlgorithmicTypingProperties]: ./theories/AlgorithmicTypingProperties.v
[LogRelConsequences]: ./theories/LogRelConsequences.v
[BundledAlgorithmicTyping]: ./theories/BundledAlgorithmicTyping.v

[autosubst-ocaml]: https://github.com/uds-psl/autosubst-ocaml
[Positivity.agda]: ./theories/Positivity.agda
