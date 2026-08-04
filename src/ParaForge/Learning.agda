{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning where

-- Learning remains a separate layer over typed computations. This facade
-- exposes feedback interfaces, categorical and parameterized lenses, explicit
-- feedback monoids, pure update policies, observable one-step training, exact
-- integer reference semantics, and backward interpretations of architecture
-- wiring. Full architecture-term interpretation remains separate.
open import ParaForge.Learning.Interface public
open import ParaForge.Learning.Algebra public
open import ParaForge.Learning.Lens public
open import ParaForge.Learning.Parametric public
open import ParaForge.Learning.Update public
open import ParaForge.Learning.Training public
open import ParaForge.Learning.Instance.Integer public
open import ParaForge.Learning.Architecture.Wiring public
open import ParaForge.Learning.Architecture.Parameter public
