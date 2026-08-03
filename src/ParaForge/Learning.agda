{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning where

-- Learning remains a separate layer over typed computations. This facade
-- currently exposes feedback interfaces, categorical lenses, and parameterized
-- lenses; updater and architecture interpretations belong to later phases.
open import ParaForge.Learning.Interface public
open import ParaForge.Learning.Lens public
open import ParaForge.Learning.Parametric public
