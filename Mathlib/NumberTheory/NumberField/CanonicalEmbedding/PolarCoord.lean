/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Polar coordinate change of variables for the mixed embedding of a number field

-/

variable (K : Type*) [Field K]

noncomputable section

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

abbrev realSpace :=
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)

def mixedSpaceToRealSpace : (mixedSpace K) ≃ₜ (realSpace K) := sorry

variable [NumberField K]

def polarCoord₀ : PartialHomeomorph (realSpace K) (realSpace K) :=
  ((PartialHomeomorph.refl _).prod (PartialHomeomorph.pi fun _ ↦ polarCoord))

def FDerivPolarCoord₀Symm : (realSpace K) → (realSpace K) →L[ℝ] (realSpace K) := sorry

theorem hasFDerivAt_polarCoord₀_symm (x : realSpace K) :
    HasFDerivAt (polarCoord₀ K) (FDerivPolarCoord₀Symm K x) x := by
  sorry


end NumberField.mixedEmbedding

end
