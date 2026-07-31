# ADR 0003: Represent actegories by a bifunctor and coherent natural isomorphisms

- **Status:** Accepted
- **Date:** 2026-07-29

## Context

The monoidal self-action milestone constructed `Para(C)` from an evaluator `P ⊗ A ⇒ B`. Definition G.1 permits the parameter category and computation category to differ: a monoidal category `M` acts on a category `C`, and evaluators instead have type `P ⊙ A ⇒ B`.

`agda-categories` supplies categories, product categories, bifunctors, natural isomorphisms, and monoidal categories, but no general actegory interface. ParaForge therefore needs a minimal interface whose coherence is strong enough for generic Para composition while recovering the completed tensor self-action exactly.

## Decision

For:

```text
M : Category oₘ ℓₘ eₘ
V : Monoidal M
C : Category o𝒞 ℓ𝒞 e𝒞
```

an `Actegory V C` stores an action bifunctor:

```text
action : Functor (Product M C) C
```

with object and morphism notation:

```text
P ⊙₀ A
p ⊙₁ f
```

The unit and associativity constraints are actual `NaturalIsomorphism` values. Their functor-level signatures are:

```text
I ⊙ -                         ≃ Id
(P ⊗ Q) ⊙ A                   ≃ P ⊙ (Q ⊙ A)
```

The second signature is represented over `Product (Product M M) C` by comparing:

```text
action ∘F (tensor ⁂ id)
action ∘F ((id ⁂ action) ∘F assocˡ M M C)
```

Using natural isomorphisms makes naturality in both parameter morphisms and computation morphisms construction data. It also supplies inverse naturality and pointwise inverse laws without duplicating fields in the actegory record.

## Coherence orientation

The forward unit component has direction:

```text
I ⊙ A ⇒ A
```

and the forward action associator has direction:

```text
(P ⊗ Q) ⊙ A ⇒ P ⊙ (Q ⊙ A)
```

These orientations are the ones needed by sequential Para composition with parameter order `Q ⊗ P`.

The triangle law is:

```text
(idP ⊙ unitorA) ∘ actionAssociator(P,I,A)
  ≈ monoidalRightUnitorP ⊙ idA
```

The interface also stores the standard left-unit coherence consequence:

```text
unitor(P ⊙ A) ∘ actionAssociator(I,P,A)
  ≈ monoidalLeftUnitorP ⊙ idA
```

This equation is derivable from actegory coherence, just as `coherence₁` is derived for a monoidal category. Keeping its witness in the interface avoids making the Para layer depend on a separate general actegory coherence theorem. The tensor self-action supplies it with `MonoidalProperties.coherence₁`.

The pentagon law is:

```text
(idP ⊙ actionAssociator(Q,R,A))
  ∘ actionAssociator(P,Q⊗R,A)
  ∘ (monoidalAssociator(P,Q,R) ⊙ idA)

≈ actionAssociator(P,Q,R⊙A)
  ∘ actionAssociator(P⊗Q,R,A)
```

All equations use the computation category's hom-setoid equality.

## Universe decision

The action functor ranges over a product of categories with independent levels. The complete record therefore lives in:

```text
Set (oₘ ⊔ ℓₘ ⊔ eₘ ⊔ o𝒞 ⊔ ℓ𝒞 ⊔ e𝒞)
```

No equality or lifting between the parameter and computation category universes is required.

The resulting actegory-based Para construction has levels:

```text
Para A X Y                         : Set (oₘ ⊔ ℓ𝒞)
Reparameterization A F G          : Set (ℓₘ ⊔ e𝒞)
Hom A X Y                         : Category (oₘ ⊔ ℓ𝒞) (ℓₘ ⊔ e𝒞) eₘ
ParaActegory A                    : Bicategory (oₘ ⊔ ℓ𝒞) (ℓₘ ⊔ e𝒞) eₘ o𝒞
```

Parameter morphisms and their equality remain in `M`; evaluator equations remain in `C`. In particular, `eₘ` governs 2-cell equality while `e𝒞` appears in the proof-carrying 2-cell level.

## Tensor self-action

Every `V : Monoidal C` induces `tensorSelfAction V : Actegory V C` by taking:

```text
P ⊙ A = P ⊗ A
```

Its action functor is the monoidal tensor bifunctor. Its unit and action associativity isomorphisms are the monoidal left unitor and associator. The actegory triangle and pentagon reduce definitionally to the corresponding `Monoidal` fields.

This instance is the required bridge back to Milestone 2. The future actegory-based Para implementation must recover the tensor self-action through this value rather than define a second unrelated instance.

## Consequences

- Phase 15 can define evaluators as `P ⊙ A ⇒ B` with truly independent parameter and computation categories.
- Reparameterization preservation will use the action on `(r , id)`.
- Sequential composition will combine parameter tensor with the forward action associator.
- G.1 cell orientation and `Q ⊗ P` parameter order remain unchanged.
- Copying and discarding are not part of `Actegory`; they still require additional parameter-side structure.
