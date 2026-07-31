# Paraforge

I love category theory and was, for quite some time, thinking about neural network architectures and how to encode them in a unified model.

Naturally I explored if papers were already out there and notably found [Categorical Deep Learning is an Algebraic Theory of All Architectures](https://arxiv.org/abs/2402.15332).
I was happy to see I am not alone with the mere idea and that people already tackled some fundamentals.

This repository is aimed at three things:

1. Purely for myself, solidifying my understanding and forcing me to think it through.
2. See if the abstraction really works across different older and newer architectures (if emergence is guaranteed)
3. Provide a hands-on library that can be used for that kind of modeling.

I use Agda, because it naturally lends itself perfectly for this kind of application.

I am also grateful to all the contributors of [Agda](https://github.com/agda/agda) and [agda-categories](https://github.com/agda/agda-categories) library creators, so I did not have to come up with an ad-hoc condensed CT library to even start implementing it.

# Current State

ParaForge provides three connected, machine-checked forms of `Para`:

- an executable, universe-polymorphic `Para(Set)` reference model;
- a generic `Para(C)` for the tensor self-action of any `agda-categories` monoidal category `C`;
- a general `Para(M ↷ C)` for a monoidal parameter category acting coherently on an independent computation category. (For the curious reader: `↷` is `\curvearrowright` and can be read as "parameter category `M` acts on the computation category `C`)

All three constructions implement the Definition G.1 orientation: a cell `F ⇒ G` carries a parameter morphism from the parameters of `G` back to those of `F`. Sequential composition uses parameter order `Q ⊗ P`. The generic constructions package their hom-categories, horizontal composition, unitors, associator, naturality, interchange, triangle, and pentagon as `agda-categories` bicategories.

The concrete model provides executable copying operations. The generic actegory model derives the same weight tying from explicit comonoid structure on parameter objects, while bare monoidal categories and actegories continue to assume no copying or deletion. Coassociativity governs repeated sharing, and optional cocommutativity governs permutation-invariant sharing.

The cartesian `Sets` specialization connects all three models at a common universe level. Identity, composition, parameter order, G.1 cells, two-way weight tying, and three-way finite-fold sharing agree under component-preserving translations and explicit product reassociation; complete proof-containing records are not equated.

Strong actegorical endofunctors now lift pseudofunctorially to the weak Para bicategory. The executable `Sets` instance for `1 + A × -` recovers the existing folding-cell interface and finite-list recurrence pointwise; `O × -` supplies the corresponding parameterized state-machine coalgebra shape. Parameter restriction and comonoid sharing commute with the lift.

Strong actegorical monads reuse `agda-categories` monad data and add exactly AS3 multiplication compatibility and AS4 unit compatibility to the existing strength. The executable exception monad `E ⊎ -` validates every failure/success branch and forgets to the strong endofunctor consumed by the existing Para pseudofunctor lift.

Their Para lift now carries weak pseudomonad data. Unit and multiplication components use parameter `I` and eliminate its action with the actegory unitor. Their invertible pseudonaturality cells compare `I ⊗ P` with `P ⊗ I` using only the canonical unit-swap built from left and right unitors—no braiding is assumed. AS4 proves unit pseudonaturality, AS3 proves multiplication pseudonaturality, and the source monad laws induce component associativity and unit cells whose parameter maps normalize in `M`.

## Stable imports

The root facade is the concrete executable API:

```agda
open import ParaForge
```

The generic APIs are namespaced to avoid collisions with concrete names such as `Para`, `idₚ`, and `_∘ₚ_`:

```agda
import ParaForge.Monoidal as Monoidal
import ParaForge.Actegory as Actegory
```

`ParaForge.Monoidal` exports the tensor self-action construction and its cartesian `Sets` specialization. `ParaForge.Actegory` exports the coherent action interface, general parameterized maps and cells, canonical parameter restriction, explicit parameter-comonoid sharing and deletion, strong endofunctors and their Para pseudofunctor lift, strong actegorical monads and their Para pseudomonad certificates, algebra/coalgebra structure-map types, the validated `Sets` instances, `ParaActegory`, and the checked specialization correspondences. Lower-level modules under `ParaForge.Para.*` and `ParaForge.Actegory.Core` should be considered internal implementation modules.

## Universe constraints

For `C : Category o ℓ e` and `M : Monoidal C`, the generic levels are:

```text
Para M A B                         : Set (o ⊔ ℓ)
Reparameterization M F G          : Set (ℓ ⊔ e)
Hom M A B                         : Category (o ⊔ ℓ) (ℓ ⊔ e) e
ParaMonoidal M                    : Bicategory (o ⊔ ℓ) (ℓ ⊔ e) e o
```

For `M : Category oₘ ℓₘ eₘ` acting on `C : Category o𝒞 ℓ𝒞 e𝒞`, the general construction has levels:

```text
Para A X Y                         : Set (oₘ ⊔ ℓ𝒞)
Reparameterization A F G          : Set (ℓₘ ⊔ e𝒞)
ParaActegory A                    : Bicategory (oₘ ⊔ ℓ𝒞) (ℓₘ ⊔ e𝒞) eₘ o𝒞
Strength A F                      : Set (oₘ ⊔ ℓₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞)
StrongEndofunctor A               : Set (oₘ ⊔ ℓₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞)
StrongMonad A                     : Set (oₘ ⊔ ℓₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞)
ParaPseudomonad S                 : Set (oₘ ⊔ ℓₘ ⊔ eₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞)
Algebra S X                       : Set (oₘ ⊔ ℓ𝒞)
Coalgebra S X                     : Set (oₘ ⊔ ℓ𝒞)
```

Specializing to `Sets ℓ` gives `Bicategory (suc ℓ) ℓ ℓ (suc ℓ)`, corresponding to concrete `ParaSet ℓ ℓ`. General actions permit parameter and computation categories to have independent levels without an implicit lifting construction.

Relative to the paper, the library now checks the general actegory setting of Definition G.1, its monoidal self-action and concrete `Set` specializations, the diagonal interpretation of weight tying, the strong-endofunctor lift underlying Example G.8, the strong-monad coherence of Definitions E.6/E.9, the algebraic folding-cell signature from Example I.1, the coalgebraic state-machine shape from Example I.3, and a finite operational form of the shared recurrent fold from Example J.1.

Lax algebra-induced comonoids, Theorem G.10, transfinite unrolling, differentiation, and training semantics remain future work.

Unlike the paper's strict presentation of Example G.8, ParaForge retains the parameter tensor unitors and action coherence explicitly. Since the current `agda-categories` release has pseudofunctors but no pseudonatural-transformation, modification, or pseudomonad records, `ParaPseudomonad` is a specialized certificate for this induced Para construction rather than a competing general bicategorical API. All current modules type-check under `--safe --without-K`, without postulates, function extensionality, proof irrelevance, or UIP.

# Why?

It's fun.

# AI Note

Yes, I am collaborating with an agent while developing this. It's just faster, what can I say.
