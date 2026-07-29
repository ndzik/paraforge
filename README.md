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

ParaForge provides two machine-checked forms of `Para`:

- an executable, universe-polymorphic `Para(Set)` reference model;
- a generic `Para(C)` for the tensor self-action of any `agda-categories` monoidal category `C`.

Both constructions implement the Definition G.1 orientation: a cell `F ⇒ G` carries a parameter morphism from the parameters of `G` back to those of `F`. Sequential composition uses parameter order `Q ⊗ P`. The generic construction packages its hom-categories, horizontal composition, unitors, associator, naturality, interchange, triangle, and pentagon as an `agda-categories` `Bicategory`.

The concrete model additionally provides executable copying operations. These express weight tying as a restriction of an untied model and support finite folding recurrent cells with either independent or shared parameters. Copying is deliberately not assumed by the bare monoidal construction.

The cartesian `Sets` specialization connects both models at a common universe level. Identity, composition, parameter order, G.1 cells, and diagonal weight tying agree pointwise. It does not identify complete proof-containing records.

## Stable imports

The root facade is the concrete executable API:

```agda
open import ParaForge
```

The generic API is namespaced to avoid collisions with concrete names such as `Para`, `idₚ`, and `_∘ₚ_`:

```agda
import ParaForge.Monoidal as Monoidal
```

`ParaForge.Monoidal` exports generic parameterized maps and cells, hom-categories, coherence cells and laws, `ParaMonoidal`, and the cartesian `Sets` specialization. Lower-level modules under `ParaForge.Para.Monoidal.*` expose implementation details and evaluator-preservation lemmas but are not the stable facade.

## Universe constraints

For `C : Category o ℓ e` and `M : Monoidal C`, the generic levels are:

```text
Para M A B                         : Set (o ⊔ ℓ)
Reparameterization M F G          : Set (ℓ ⊔ e)
Hom M A B                         : Category (o ⊔ ℓ) (ℓ ⊔ e) e
ParaMonoidal M                    : Bicategory (o ⊔ ℓ) (ℓ ⊔ e) e o
```

Specializing to `Sets ℓ` gives `Bicategory (suc ℓ) ℓ ℓ (suc ℓ)`, corresponding to concrete `ParaSet ℓ ℓ`. The concrete model still permits independent data and parameter levels `o` and `p`; the tensor self-action does not recover that freedom without an explicit lifting or a more general action.

Relative to the paper, the library currently checks the concrete `Set` instance of Definition G.1, the generic monoidal self-action case, the diagonal interpretation of weight tying, the folding-cell signature from Example I.1, and a finite operational form of the shared recurrent fold from Example J.1.

General actegories, strong 2-monads, lax algebra machinery, Theorem G.10, transfinite unrolling, differentiation, and training semantics remain future work. All current modules type-check under `--safe --without-K`, without postulates, function extensionality, proof irrelevance, or UIP.

# Why?

It's fun.

# AI Note

Yes, I am collaborating with an agent while developing this. It's just faster, what can I say.
