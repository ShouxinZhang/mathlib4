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



section prodMap

variable {R : Type*} {M₁ : Type*} {M₂ : Type*} [CommRing R]
  [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
  [Module.Free R M₁] [Module.Free R M₂] [Module.Finite R M₁] [Module.Finite R M₂]
  (f₁ : Module.End R M₁) (f₂ : Module.End R M₂)

theorem LinearMap.prodMap_det :
    (LinearMap.prodMap f₁ f₂).det = f₁.det * f₂.det := by
  classical
  let b₁ := Module.Free.chooseBasis R M₁
  let b₂ := Module.Free.chooseBasis R M₂
  have := LinearMap.toMatrix_prodMap b₁ b₂ f₁ f₂
  rw [← det_toMatrix (b₁.prod b₂), ← det_toMatrix b₁, ← det_toMatrix b₂, toMatrix_prodMap,
    Matrix.det_fromBlocks_zero₂₁, det_toMatrix]

end prodMap


variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding ENNReal MeasureTheory
  MeasureTheory.Measure Real

noncomputable section realSpace

abbrev realSpace :=
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)

variable [NumberField K]

open Classical in
instance : IsAddHaarMeasure (volume : Measure (realSpace K)) := prod.instIsAddHaarMeasure _ _

def polarCoord₀ : PartialHomeomorph (realSpace K) (realSpace K) :=
  ((PartialHomeomorph.refl _).prod (PartialHomeomorph.pi fun _ ↦ polarCoord))

@[simp]
theorem polarCoord₀_symm_apply (x : realSpace K) :
    (polarCoord₀ K).symm x = (x.1, fun w ↦ polarCoord.symm (x.2 w)) := rfl

@[simp]
theorem polarCoord₀_source :
    (polarCoord₀ K).source = Set.univ ×ˢ (Set.univ.pi fun _ ↦ polarCoord.source) := rfl

private theorem abs_of_mem_polarCoord₀_target {x : realSpace K}
    (hx : x ∈ (polarCoord₀ K).target) (w : {w // IsComplex w}) :
    |(x.2 w).1| = (x.2 w).1 :=
  abs_of_pos (hx.2 w trivial).1

open ContinuousLinearMap in
def FDerivPolarCoord₀Symm : realSpace K → realSpace K →L[ℝ] realSpace K :=
  fun x ↦ (fst ℝ _ _).prod <| (FDerivPiPolarCoordSymm x.2).comp (snd ℝ _ _)

theorem hasFDerivAt_polarCoord₀_symm (x : realSpace K) :
    HasFDerivAt (polarCoord₀ K).symm (FDerivPolarCoord₀Symm K x) x := by
  classical
  exact (hasFDerivAt_id x.1).prodMap x (hasFDerivAt_pi_polarCoord_symm x.2)

open Classical in
theorem det_fderiv_polarCoord₀_symm (x : realSpace K) :
    (FDerivPolarCoord₀Symm K x).det = ∏ w : {w // IsComplex w}, (x.2 w).1 := by
  have : (FDerivPolarCoord₀Symm K x).toLinearMap =
      LinearMap.prodMap (LinearMap.id) (FDerivPiPolarCoordSymm x.2).toLinearMap := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.prodMap_det, LinearMap.det_id, one_mul,
    ← ContinuousLinearMap.det, det_fderiv_pi_polarCoord_symm]

open Classical in
theorem polarCoord₀_symm_target_ae_eq_univ :
    (polarCoord₀ K).symm '' (polarCoord₀ K).target =ᵐ[volume] Set.univ := by
  rw [← Set.univ_prod_univ, volume_eq_prod, (polarCoord₀ K).symm_image_target_eq_source,
    polarCoord₀_source, ← polarCoord.symm_image_target_eq_source, ← Set.piMap_image_univ_pi]
  exact set_prod_ae_eq (by rfl) pi_polarCoord_symm_target_ae_eq_univ

open Classical in
theorem integral_comp_polarCoord₀_symm  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realSpace K → E) :
    ∫ x in (polarCoord₀ K).target, (∏ w : {w // IsComplex w}, (x.2 w).1) •
      f ((polarCoord₀ K).symm x) = ∫ x, f x := by
  rw [← setIntegral_univ (f := f), ← setIntegral_congr_set (polarCoord₀_symm_target_ae_eq_univ K)]
  convert (integral_image_eq_integral_abs_det_fderiv_smul volume
    (polarCoord₀ K).open_target.measurableSet
    (fun x _ ↦ (hasFDerivAt_polarCoord₀_symm K x).hasFDerivWithinAt)
    (polarCoord₀ K).symm.injOn f).symm using 1
  refine setIntegral_congr_fun (polarCoord₀ K).open_target.measurableSet fun x hx ↦ ?_
  simp_rw [det_fderiv_polarCoord₀_symm, Finset.abs_prod, abs_of_mem_polarCoord₀_target K hx]

open Classical in
theorem lintegral_comp_polarCoord₀_symm (f : realSpace K → ℝ≥0∞) :
    ∫⁻ x in (polarCoord₀ K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((polarCoord₀ K).symm x) = ∫⁻ x, f x := by
  rw [← setLIntegral_univ f, ← setLIntegral_congr (polarCoord₀_symm_target_ae_eq_univ K)]
  convert (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (polarCoord₀ K).open_target.measurableSet
    (fun x _ ↦ (hasFDerivAt_polarCoord₀_symm K x).hasFDerivWithinAt)
    (polarCoord₀ K).symm.injOn f).symm using 1
  refine setLIntegral_congr_fun (polarCoord₀ K).open_target.measurableSet ?_
  filter_upwards with x hx
  simp_rw [det_fderiv_polarCoord₀_symm, Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦
    abs_nonneg _), abs_of_mem_polarCoord₀_target K hx]

end realSpace

noncomputable def mixedSpaceToRealSpace : mixedSpace K ≃ₜ realSpace K :=
  (Homeomorph.refl _).prodCongr <| .piCongrRight fun _ ↦ Complex.equivRealProdCLM.toHomeomorph

@[simp]
theorem mixedSpaceToRealSpace_apply (x : mixedSpace K) :
    mixedSpaceToRealSpace K x = (x.1, fun w ↦ ((x.2 w).re, (x.2 w).im)) := rfl

variable [NumberField K]

open Classical in
theorem volume_preserving_mixedSpaceToRealSpace_symm :
    MeasurePreserving (mixedSpaceToRealSpace K).symm :=
  (MeasurePreserving.id _).prod <|
    volume_preserving_pi fun _ ↦  Complex.volume_preserving_equiv_real_prod.symm

protected noncomputable def polarCoord : PartialHomeomorph (mixedSpace K) (realSpace K) :=
  (mixedSpaceToRealSpace K).transPartialHomeomorph (polarCoord₀ K)

protected theorem polarCoord_target :
    (mixedEmbedding.polarCoord K).target =
      Set.univ ×ˢ (Set.univ.pi fun _ ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) := rfl

@[simp]
protected theorem polarCoord_symm_apply (x : realSpace K) :
    (mixedEmbedding.polarCoord K).symm x = (x.1, fun w ↦ Complex.polarCoord.symm (x.2 w)) := rfl

open Classical

protected theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedSpace K → E) :
    ∫ x in (mixedEmbedding.polarCoord K).target,
      (∏ w : {w // IsComplex w}, (x.2 w).1) • f ((mixedEmbedding.polarCoord K).symm x) =
        ∫ x, f x := by
  rw [← (volume_preserving_mixedSpaceToRealSpace_symm K).integral_comp
    (mixedSpaceToRealSpace K).symm.measurableEmbedding, ← integral_comp_polarCoord₀_symm]
  rfl

protected theorem lintegral_comp_polarCoord_symm (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (mixedEmbedding.polarCoord K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((mixedEmbedding.polarCoord K).symm x) = ∫⁻ x, f x := by
  rw [← ( volume_preserving_mixedSpaceToRealSpace_symm K).lintegral_comp_emb
    (mixedSpaceToRealSpace K).symm.measurableEmbedding, ← lintegral_comp_polarCoord₀_symm]
  rfl

theorem toto {s₁ : Set ({w // IsReal w} → ℝ)} {s₂ : Set ({w // IsComplex w} → ℂ)} :
    (mixedEmbedding.polarCoord K).symm ⁻¹' s₁ ×ˢ s₂ =
      s₁ ×ˢ (Pi.map (fun _ ↦ Complex.polarCoord.symm) ⁻¹' s₂) := by
  rfl

theorem zap {s₁ : Set ({w // IsReal w} → ℝ)} {s₂ : Set ({w // IsComplex w} → ℂ)} :
    (mixedEmbedding.polarCoord K).target ∩ (mixedEmbedding.polarCoord K).symm ⁻¹' s₁ ×ˢ s₂ =
      s₁ ×ˢ
      ((Set.univ.pi fun _ ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) ∩
        (Pi.map fun _ ↦ ↑Complex.polarCoord.symm) ⁻¹' s₂) := by
  rw [mixedEmbedding.polarCoord_target, toto, Set.prod_inter_prod, Set.univ_inter]

protected theorem volume_prod {s₁ : Set ({w // IsReal w} → ℝ)} {s₂ : Set ({w // IsComplex w} → ℂ)}
    (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂) :
    volume (s₁ ×ˢ s₂ : Set (mixedSpace K)) = volume s₁ *
      ∫⁻ x in
        (Set.univ.pi fun _ ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) ∩
          (Pi.map fun _ ↦ Complex.polarCoord.symm) ⁻¹' s₂,
            (∏ w : {w // IsComplex w}, .ofReal (x w).1) := by
  have h_mes : MeasurableSet ((Set.univ.pi fun x ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) ∩
      (Pi.map fun x ↦ ↑Complex.polarCoord.symm) ⁻¹' s₂) :=
    measurableSet_pi_polarCoord_target.inter <| hs₂.preimage <| measurable_pi_iff.mpr
      fun w ↦ Complex.continuous_polarCoord_symm.measurable.comp (measurable_pi_apply w)
  calc
    _ = ∫⁻ (x : realSpace K), (mixedEmbedding.polarCoord K).target.indicator
          (fun p ↦ (∏ w, .ofReal (p.2 w).1) *
            (s₁ ×ˢ s₂).indicator 1 ((mixedEmbedding.polarCoord K).symm p)) x := ?_
    _ = ∫⁻ (x : realSpace K), ((mixedEmbedding.polarCoord K).target ∩
          (mixedEmbedding.polarCoord K).symm ⁻¹' s₁ ×ˢ s₂).indicator
            (fun p ↦ (∏ w, .ofReal (p.2 w).1) * 1) x := ?_
    _ =  ∫⁻ (x : realSpace K), (s₁.indicator 1 x.1) *
          (((Set.univ.pi fun x ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) ∩
            (Pi.map fun x ↦ ↑Complex.polarCoord.symm) ⁻¹' s₂).indicator
              (fun p ↦ 1 * ∏ w, .ofReal (p w).1) x.2)
               := ?_
    _ = volume s₁ * ∫⁻ x in (Set.univ.pi fun x ↦ Set.Ioi 0 ×ˢ Set.Ioo (-π) π) ∩
        (Pi.map fun x ↦ ↑Complex.polarCoord.symm) ⁻¹' s₂,
          ∏ w : {w : InfinitePlace K // w.IsComplex}, ENNReal.ofReal (x w).1 := ?_
  · rw [← lintegral_indicator_one (hs₁.prod hs₂), ← mixedEmbedding.lintegral_comp_polarCoord_symm,
      ← lintegral_indicator (mixedEmbedding.polarCoord K).open_target.measurableSet]
  · congr with _
    rw [Set.inter_indicator_mul, Set.indicator_mul_left, ← Set.indicator_comp_right, Pi.one_comp,
      Pi.one_def]
  · congr with _
    rw [Set.indicator_mul_right, mul_comm, Set.indicator_mul_left, ← mul_assoc, ← Pi.one_def,
      ← Pi.one_def, ← Set.indicator_prod_one, zap]
  · simp_rw [one_mul, Pi.one_def]
    rw [volume_eq_prod, lintegral_prod_mul (aemeasurable_const.indicator hs₁)
      ((Measurable.aemeasurable (by fun_prop)).indicator h_mes), ← Pi.one_def,
      lintegral_indicator_one hs₁, lintegral_indicator h_mes]

end NumberField.mixedEmbedding
