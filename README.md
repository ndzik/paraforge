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

ParaForge provides a universe-polymorphic, executable model of `Para(Set)` in which:

- parameterized maps `P × A → B` can be evaluated and composed;
- behavior-preserving reparameterizations can be constructed and composed vertically and horizontally;
- copy maps express weight tying as a restriction of an untied model;
- finite folding recurrent cells can be unrolled with either independent or shared parameters;
- the shared unrolling is witnessed by a repeated-diagonal reparameterization.

The concrete construction is packaged as an `agda-categories` `Bicategory`. Its hom-categories, composition bifunctor, unitors, associator, naturality, interchange, triangle, and pentagon laws are machine checked. This makes identity insertion and reassociation of parameter products coherent rather than treating products as definitionally strict.

Relative to the paper, the library currently checks the concrete `Set` instance of Definition G.1, including its target-to-source 2-cell orientation, the diagonal interpretation of weight tying, the folding-cell signature from Example I.1, and a finite operational form of the shared recurrent fold from Example J.1.

It does not yet formalize general actegories, strong 2-monads, lax algebra machinery, Theorem G.10, transfinite unrolling, differentiation, or training semantics. All current modules type-check under `--safe --without-K`, without postulates, function extensionality, proof irrelevance, or UIP.

# Why?

It's fun.

# AI Note

Yes, I am collaborating with an agent while developing this. It's just faster, what can I say.
