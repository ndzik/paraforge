{-# OPTIONS --safe --without-K #-}

module ParaForge.Learning where

-- Learning remains a separate layer over typed computations. This facade
-- exposes feedback interfaces, categorical and parameterized lenses, pure
-- update policies, observable one-step training, and the exact integer
-- reference interpretation. Architecture interpretations remain separate.
open import ParaForge.Learning.Interface public
open import ParaForge.Learning.Lens public
open import ParaForge.Learning.Parametric public
open import ParaForge.Learning.Update public
open import ParaForge.Learning.Training public
open import ParaForge.Learning.Instance.Integer public
