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
- a general `Para(M ↷ C)` for a monoidal parameter category acting coherently on an independent computation category.

All three constructions implement the Definition G.1 orientation: a cell `F ⇒ G` carries a parameter morphism from the parameters of `G` back to those of `F`. Sequential composition uses parameter order `Q ⊗ P`. The generic constructions package their hom-categories, horizontal composition, unitors, associator, naturality, interchange, triangle, and pentagon as `agda-categories` bicategories.

The concrete model additionally provides executable copying operations. These express weight tying as a restriction of an untied model and support finite folding recurrent cells with either independent or shared parameters. Copying is deliberately not assumed by the bare monoidal construction.

The cartesian `Sets` specialization connects the concrete and monoidal models at a common universe level. The tensor self-action specialization similarly connects the actegory and monoidal models. Their identity, composition, parameter order, and G.1 cells agree under component-preserving translations; complete proof-containing bicategory records are not equated.

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

`ParaForge.Monoidal` exports the tensor self-action construction and its cartesian `Sets` specialization. `ParaForge.Actegory` exports the coherent action interface, general parameterized maps and cells, `ParaActegory`, and the checked tensor self-action correspondence. Lower-level modules under `ParaForge.Para.*` and `ParaForge.Actegory.Core` remain implementation modules.

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
```

Specializing to `Sets ℓ` gives `Bicategory (suc ℓ) ℓ ℓ (suc ℓ)`, corresponding to concrete `ParaSet ℓ ℓ`. General actions permit parameter and computation categories to have independent levels without an implicit lifting construction.

Relative to the paper, the library now checks the general actegory setting of Definition G.1, its monoidal self-action and concrete `Set` specializations, the diagonal interpretation of weight tying, the folding-cell signature from Example I.1, and a finite operational form of the shared recurrent fold from Example J.1.

Cartesian copying/discarding, strong 2-monads, lax algebra machinery, Theorem G.10, transfinite unrolling, differentiation, and training semantics remain future work. All current modules type-check under `--safe --without-K`, without postulates, function extensionality, proof irrelevance, or UIP.

# Why?

It's fun.

# AI Note

Yes, I am collaborating with an agent while developing this. It's just faster, what can I say.
