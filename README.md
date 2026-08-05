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

ParaForge can describe, compose, execute, and analyze typed parameterized architectures without committing them to a numerical machine-learning backend.

The bulk and most interesting parts of the paper are implemented.
Right now I am drafting an updated category that explicitly models "learning".
The hypothesis is, that this overview might give a little more insights into extracting "structural components" of trained models.

## Parameterized computations

A parameterized computation from `A` to `B` consists of a parameter object `P` and an evaluator `P ⊙ A → B`. ParaForge provides this construction at three levels:

- an executable, universe-polymorphic `Para(Set)` reference model;
- `Para(C)` for the tensor self-action of a monoidal category `C`;
- `Para(M ↷ C)` for parameters in a monoidal category `M` acting on an independent computation category `C`.

Parameterized computations support identity and sequential composition. Composition combines the later parameters `Q` with the earlier parameters `P` in the order `Q ⊗ P`. The generic constructions form weak bicategories with explicit unitors, associators, naturality, interchange, triangle, and pentagon coherence.

## Reparameterization and sharing

A transformation `F ⇒ G` follows Definition G.1 and carries a parameter map from the parameters of `G` back to those of `F`. This makes reparameterization a behavior-preserving restriction: the target architecture can only realize behavior already represented by the source.

ParaForge supports:

- arbitrary typed parameter restriction;
- weight tying by restriction along a copy map;
- parameter deletion through a counit;
- repeated sharing governed by coassociativity;
- optional permutation-invariant sharing when cocommutativity is available;
- identity, vertical, and horizontal composition of architecture transformations.

Copying and deletion are never assumed from a bare monoidal category or actegory. They require an explicit comonoid on the relevant parameter object.

## Architecture language

`ParaForge.Architecture` provides an intrinsically typed Agda-embedded architecture language. An architecture records its parameter context, input interface, and output interface in its type. The language includes:

- primitive operations from an extensible typed signature;
- sequential and parallel composition;
- activation fan-out and structural data wiring;
- residual composition;
- explicit parameter bindings and lexical parameter sharing;
- independent and shared finite repetition;
- typed architecture transformations.

The core distinguishes sequential `CoreArch` syntax from the cartesian `CartesianArch` dataflow extension. A `Network` keeps its untied primitive occurrences separate from the external parameter binding that controls independence, deletion, permutation, or sharing.

A sequential classifier can be written as:

```agda
mlp =
  dense 2 3 >>>
  relu 3 >>>
  dense 3 1 >>>
  softmax 1
```

Transformer parameters are ordinary, intrinsically typed Agda references. Named branches can share one lexical parameter scope with `_>>>ˢ_`, while `residualTokens` inserts activation fan-out and recombination:

```agda
attentionBranch =
  layerNormUsing firstNormParameter >>>ˢ
  selfAttentionUsing attentionParameter

encoderBlock =
  residualTokens sequenceLength modelWidth attentionBranch >>>ˢ
  residualTokens sequenceLength modelWidth feedForwardBranch
```

`repeatIndependent` gives each block its own external parameter context. `repeatSharedNeural` uses one context for every occurrence, covering architectures such as ALBERT-style shared Transformer stacks.

A separate backend-neutral tensor specialization provides scalar, vector, grid, unit, and structural-product shapes together with closed linear, convolution, activation, and addition codes. Its NCA example describes a fixed identity/Sobel perception bank, a two-layer trainable pointwise update, explicit residual fan-out, and four shared update steps over a `16 × 16 × 4` grid. The four steps retain two external trainable parameters and eight parameter-consuming occurrences. These are typed architecture codes; they do not implement numerical tensor kernels in Agda.

The NCA also compiles into a closed, shape-indexed export target whose primitives refer directly to typed external parameter slots. An explicit `compileSharedRollout` preserves repetition as `Repeat 4` without changing the source architecture syntax or guessing repetition from an expanded composition. A pure canonical encoder produces the versioned `examples/nca.json`; its two canonical parameter ids are reused in the order `[1,0,1,0,1,0,1,0]`. The independent standard-library-only parser in `runtime/ir.py` rejects unknown fields and versions, mistyped references, incompatible shapes, malformed structural wiring, and non-endomorphic repeats. It validates architecture only and imports no numerical backend.

## Interpretation and inspection

The same architecture description can be interpreted in more than one way:

- the executable `Sets` model runs lightweight reference evaluators and makes parameter order and sharing observable;
- the symbolic model reports typed nodes, composition depth, raw parameter occurrences, external parameter count, and sharing classes.

For example, two shared Transformer blocks have eight parameter-consuming occurrences but only four external parameter variables. Their symbolic sharing classes are:

```text
[0, 1, 2, 3, 0, 1, 2, 3]
```

The executable architecture model intentionally uses small scalar stand-ins. The tensor signature is currently declarative: ParaForge does not yet provide numerical tensor kernels, automatic differentiation, production numerical optimization, or integration with an ML runtime. Attention is represented as an architecture-level primitive rather than expanded into tensor contractions.

## Feedback lenses

`ParaForge.Learning` provides a separate executable layer for bidirectional computations. A `FeedbackInterface` keeps forward values distinct from the feedback sent against them. A `Lens` supplies forward evaluation and backward feedback propagation, with identity and sequential composition packaged as an `agda-categories` category under pointwise behavioral equality.

`ParametricLens` additionally separates parameter values from parameter signals. Composition retains the ParaForge order `Q × P`, propagates feedback in reverse execution order, and returns signals as `Q♭ × P♭`. The implementation currently recomputes intermediate activations during propagation.

`UpdatePolicy` interprets parameter signals independently and may carry state. A `FeedbackSource` closes the output boundary, and `trainStep` exposes the output, output feedback, parameter and input signals, next updater state, and next parameter as one pure result. The exact integer reference supplies explicit reverse rules for translation, affine, and square operations, plus gradient descent and no-update policies. These are reference semantics rather than an automatic differentiation system.

Backward structural wiring is explicit as well. `FeedbackMonoid` supplies ordered aggregation for copied activations, while optional commutativity remains separate evidence. `DataflowLearningModel` interprets copy, discard, swap, and reassociation as lenses and records compatibility between tensor encodings and feedback monoids. `ParameterLearningModel` gives declared reparameterizations their own backward transport; cartesian selections use `AllShareable` evidence to initialize deleted signals and aggregate repeated occurrences in order. Thus forward weight tying remains restriction along copying, while reverse sharing combines occurrence signals into one external parameter signal.

`ArchitectureLearningModel` is the backend-neutral interpretation boundary. A model supplies typed value and feedback carriers plus primitive behavior, and the generic fold interprets existing `CoreArch`, `CartesianArch`, `Network`, and architecture cells without knowing about arrays, devices, autodiff, or a particular runtime. A separate structural interpretation records forward and reverse nodes, normalized parameter destinations, and aggregation sites. Signature-declared opaque reparameterizations remain unknown rather than receiving invented reverse behavior.

The existing MLP, finite independent/shared sequences, pre-normalized Transformer block, and independent/shared Transformer stacks have structural learning interpretations. Their checks expose reverse primitive order, residual fan-out, and shared occurrence aggregation. In particular, the shared two-block Transformer retains eight parameter-consuming occurrences, four external parameters, and aggregation destinations `[0, 1, 2, 3]`. A symbolic feedback-event witness agrees forward with the existing lightweight `Sets` semantics but implements no neural derivatives or updates.

The categorical boundary is independent of numerical runtime choice. External backends own tensor kernels, numerical derivatives, automatic differentiation, optimizers, devices, and training loops. JAX is the first planned backend, not an assumption of the architecture or learning interfaces. Tensor execution, numerical neural derivatives, and runtime training loops are not yet provided.

## Algebraic structure and recurrence

The generic API also provides:

- strong actegorical endofunctors and their pseudofunctorial lift to `Para`;
- strong actegorical monads and specialized weak pseudomonad data on `Para`;
- algebras and coalgebras for parameterized structure maps;
- lax algebras and structural lax algebra morphisms;
- extraction of parameter comonoids from lax algebra coherence;
- finite shared folds and parameterized state-machine examples.

The executable examples include folding cells, finite-list folds, exception algebras, unfolding coalgebra shapes, MLPs, Transformer blocks, and independent or shared architecture repetition.

## Imports

The root facade is the concrete executable API:

```agda
open import ParaForge
```

The generic APIs are namespaced to avoid collisions with concrete names such as `Para`, `idₚ`, and `_∘ₚ_`:

```agda
import ParaForge.Monoidal as Monoidal
import ParaForge.Actegory as Actegory
```

The architecture and learning languages are exposed through separate facades. Importing the learning facade qualified keeps its generic `Value` projection distinct from the executable architecture model's `Value` family:

```agda
open import ParaForge.Architecture
import ParaForge.Learning as Learning
```

`ParaForge.Monoidal` exports the tensor self-action construction and its cartesian `Sets` specialization. `ParaForge.Actegory` exports the coherent action interface, generic parameterized maps and cells, parameter restriction, comonoid sharing and deletion, strong endofunctors and monads, their Para lifts, lax algebras, induced parameter comonoids, algebra and coalgebra structure maps, `Sets` instances, and `ParaActegory`. Lower-level modules under `ParaForge.Para.*` and `ParaForge.Actegory.Core` are implementation modules.

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
LaxAlgebra S X                    : Set (oₘ ⊔ ℓₘ ⊔ eₘ ⊔ ℓ𝒞 ⊔ e𝒞)
Algebra S X                       : Set (oₘ ⊔ ℓ𝒞)
Coalgebra S X                     : Set (oₘ ⊔ ℓ𝒞)
```

Specializing to `Sets ℓ` gives `Bicategory (suc ℓ) ℓ ℓ (suc ℓ)`, corresponding to concrete `ParaSet ℓ ℓ`. General actions permit parameter and computation categories to have independent levels without an implicit lifting construction.

## Formal guarantees and scope

ParaForge retains weak monoidal, actegory, and bicategorical coherence explicitly rather than strictifying parameter products. Equalities between transformations are stated through the relevant categorical hom-setoids instead of propositional equality of proof-containing records.

The formalization covers the general actegory form of Definition G.1, monoidal self-actions and concrete `Set` specializations, diagonal weight tying, strong endofunctor and monad lifts, lax algebra parameter comonoids, algebraic folding cells, coalgebraic state-machine cells, and finite shared recurrence.

`ParaPseudomonad` is a Para-specific certificate because `agda-categories` does not provide general records for pseudonatural transformations, modifications, or pseudomonads. It does not replace a general bicategorical API.

All Agda modules type-check under `--safe --without-K`, without postulates, function extensionality, proof irrelevance, or UIP. Tensor runtimes, infinite unrolling, streams, differentiation, optimization, and training semantics are outside the implemented scope.

# Why?

It's fun.

# AI Note

Yes, I am collaborating with an agent while developing this. It's just faster, what can I say.
