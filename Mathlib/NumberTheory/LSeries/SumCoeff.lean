/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic

/-!
  # Docs
-/

open Finset Filter MeasureTheory Topology Complex Asymptotics

-- Clear the Asymptotics

section lemmas

-- modified function

theorem modif₀ (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    (fun n ↦ if n = 0 then 0 else f n) n = f n := by
  simp_rw [if_neg hn]

theorem modif₁ (f : ℕ → ℂ) :
    (fun n ↦ if n = 0 then 0 else f n) =ᶠ[atTop] f := by
  filter_upwards [eventually_ne_atTop 0] with n hn using modif₀ f hn

theorem modif₂₀ {𝕜 : Type*} [RCLike 𝕜] (f : ℕ → 𝕜) (n : ℕ) :
    ∑ k ∈ Icc 1 n, (if k = 0 then 0 else f k) = ∑ k ∈ Icc 1 n, f k := by
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne']

theorem modif₂ (f : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, ‖if k = 0 then 0 else f k‖ = ∑ k ∈ Icc 1 n, ‖f k‖ := by
  simp_rw [apply_ite, norm_zero]
  exact modif₂₀ _ _

theorem modif₃ {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → 𝕜} (hf : f 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, f k = ∑ k ∈ Icc 1 n, f k := by
  rw [← Nat.Icc_insert_succ_left n.zero_le, sum_insert (mem_Icc.not.mpr (by omega)),
    hf, zero_add, zero_add]

-- cpow / rpow

theorem new_aux₂ {t : ℝ} {c : ℂ} (ht : 0 < t):
    ‖(t : ℂ) ^ c‖ = t ^ c.re := by
  rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos ht]

theorem new_aux₀ {c : ℂ} (hc : c ≠ 0) :
    Set.EqOn (fun t : ℝ ↦ - c * (t : ℂ) ^ (- (c + 1)))
      (deriv fun t : ℝ ↦ (t : ℂ) ^ (- c)) (Set.Ioi 1) := by
  intro t ht
  rw [(deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne' (neg_ne_zero.mpr hc)), neg_add']

-- Should be Set.EqOn too
theorem new_aux₃' {t : ℝ} {c : ℂ} (ht : 0 < t) :
    (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ (- c)‖) t = - c.re * t ^ (- c.re - 1) := by
  rw [← Real.deriv_rpow_const (Or.inl ht.ne')]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_gt_nhds ht] with x hx using new_aux₂ hx

theorem new_aux₂' {c : ℂ} :
    Set.EqOn (fun t ↦ - c.re * t ^ (- (c.re + 1)))
      (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ (- c)‖) (Set.Ioi 1) := by
  intro t ht
  rw [new_aux₃' (zero_lt_one.trans ht), neg_add']

-- integrability on Ioi1

theorem integ₁ {a s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t : ℝ ↦ a * t ^ (- s)) (Set.Ioi 1) :=
  ((integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by rwa [neg_lt_neg_iff])).const_mul _

theorem integ₂ {a c : ℂ} (hc : 1 < c.re) :
    IntegrableOn (fun t : ℝ ↦ a * t ^ (- c)) (Set.Ioi 1) :=
  ((integrableOn_Ioi_cpow_iff zero_lt_one).mpr (by rwa [neg_re, neg_lt_neg_iff])).const_mul _

theorem new_aux₃ {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ (- c)‖) (Set.Ioi 1) :=
  IntegrableOn.congr_fun (integ₁ (by rwa [lt_add_iff_pos_left])) new_aux₂' measurableSet_Ioi

theorem aux₁₁ {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (deriv fun x : ℝ ↦ (x : ℂ) ^ (- c)) (Set.Ioi 1) := by
  refine IntegrableOn.congr_fun ?_ (new_aux₀ (ne_zero_of_re_pos hc)) measurableSet_Ioi
  exact integ₂ (by rwa [add_re, one_re, lt_add_iff_pos_left])

-- asymptotics

theorem asymp₁ (c : ℂ) :
    (fun t : ℝ ↦ ‖(t : ℂ) ^ (- c)‖) =O[atTop] fun t ↦ t ^ (- c.re) := by
  refine EventuallyEq.isBigO ?_
  filter_upwards [eventually_gt_atTop 0] with t ht using by rw [new_aux₂ ht, neg_re]

theorem asymp₂ (c : ℂ) :
    (fun t : ℝ ↦ (t : ℂ) ^ (- c)) =O[atTop] fun t ↦ t ^ (- c.re) :=
  isBigO_norm_left.mp (asymp₁ c)

theorem asymp₃ {c : ℂ} (hc : c ≠ 0) :
    (deriv fun t : ℝ ↦ (t : ℂ) ^ (- c)) =O[atTop] fun t ↦ t ^ (- (c + 1).re) := by
  refine ((asymp₂ (c + 1)).const_mul_left (- c)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 1] with t ht using by rw [← new_aux₀ hc ht]

theorem new_aux₄ {𝕜 : Type*} [RCLike 𝕜] {f g : ℝ → 𝕜} (a b c : ℝ)
    (hf : f =O[atTop] fun t ↦ (t : ℝ) ^ a)
    (hg : g =O[atTop] fun t ↦ (t : ℝ) ^ b) (h : a + b ≤ c) :
    (f * g) =O[atTop] fun t ↦ (t : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

theorem new_aux₅ {𝕜 : Type*} [RCLike 𝕜] {f g : ℕ → 𝕜} (a b c : ℝ)
    (hf : f =O[atTop] fun n ↦ (n : ℝ) ^ a)
    (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ b) (h : a + b ≤ c) :
    (f * g) =O[atTop] fun n ↦ (n : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

theorem new_aux₆ {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} {f : ℕ → 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hbO : (fun n ↦ ∑ k ∈ Icc m n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun t : ℝ ↦ ∑ k ∈ Icc m ⌊t⌋₊, f k) =O[atTop] fun t : ℝ ↦ t ^ r := by
  refine (hbO.comp_tendsto tendsto_nat_floor_atTop).trans <|
    isEquivalent_nat_floor.isBigO.rpow hr ?_
  filter_upwards [eventually_ge_atTop 0] with _ ht using ht

end lemmas

section summable

variable {f : ℕ → ℂ} {r : ℝ} {s : ℂ}

private theorem LSeriesSummable_of_sum_norm_bigO_aux (hf : f 0 = 0)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hr : 0 ≤ r) (hs : r < s.re) :
     LSeriesSummable f s := by
  have h₁ : -s ≠ 0 := neg_ne_zero.mpr <| ne_zero_of_re_pos (hr.trans_lt hs)
  have h₂ : (-s).re + r ≤ 0 := by
    rw [neg_re, neg_add_nonpos_iff]
    exact hs.le
  have h₃ : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ ↦ ‖(x : ℂ) ^ (-s)‖) t := by
    intro t ht
    have ht' : t ≠ 0 := (zero_lt_one.trans_le ht).ne'
    exact (differentiableAt_id.ofReal_cpow_const ht' h₁).norm ℝ <|
      (cpow_ne_zero_iff h₁).mpr <| ofReal_ne_zero.mpr ht'
  have h₄ : (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ (- s)‖) =ᶠ[atTop] fun t ↦ - s.re * t ^ (- s.re - 1) := by
    filter_upwards [eventually_gt_atTop 0] with t ht using new_aux₃' ht
  change Summable (fun n ↦ LSeries.term f s n)
  simp_rw [LSeries.term_def' hf]
  refine summable_mul_of_bigO_atTop' (f := fun t ↦ (t : ℂ) ^ (-s))
    (g := fun t ↦ t ^ ((- s - 1).re + r)) _ h₃ ?_ ?_ ?_ ?_
  · exact integrableOn_Ici_iff_integrableOn_Ioi.mpr (new_aux₃ (hr.trans_lt hs))
  · refine (new_aux₅ ((- s).re) r 0 ?_ hO h₂).congr_right (by simp)
    exact (asymp₁ _).natCast_atTop
  · refine new_aux₄ ((- s).re - 1) r _ ?_ ?_ (by rw [sub_re, one_re])
    · exact (EventuallyEq.isBigO h₄).of_const_mul_right
    · exact new_aux₆ hr hO
  · apply integrableAtFilter_rpow_atTop
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]

theorem LSeriesSummable_of_sum_norm_bigO
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hr : 0 ≤ r) (hs : r < s.re) :
    LSeriesSummable f s := by
  refine LSeriesSummable.congr' _ (modif₁ f) ?_
  refine LSeriesSummable_of_sum_norm_bigO_aux (by rw [if_pos rfl]) ?_ hr hs
  simpa only [modif₂] using hO

end summable

section integral_repr

private theorem LSeries_eq_mul_integral_aux {f : ℕ → ℂ} (hf : f 0 = 0) {r : ℝ} (hr : 0 ≤ r) {s : ℂ}
    (hs : r < s.re) (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- s - 1) := by
  have h₁ : (-s - 1).re + r < -1 := by
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]
  have h₂ : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  have h₃ : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t :=
    fun t ht ↦ differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne'
      (neg_ne_zero.mpr h₂)
  simp_rw [← modif₃ hf] at hO
  rw [← integral_mul_left]
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).mpr hS.hasSum.tendsto_sum_nat) ?_
  simp_rw [Nat.range_succ_Icc_zero, LSeries.term_def' hf]
  convert tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := fun x ↦ (x : ℂ) ^ (-s)) (l := 0)
    ?_ hf h₃ ?_ ?_ ?_ (integrableAtFilter_rpow_atTop h₁)
  · rw [zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [← new_aux₀ h₂ ht, modif₃ hf]
    ring_nf
  · exact integrableOn_Ici_iff_integrableOn_Ioi.mpr <| aux₁₁ (hr.trans_lt hs)
  · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (- (s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by rwa [sub_pos])).comp tendsto_natCast_atTop_atTop
    refine Asymptotics.IsBigO.trans_tendsto ?_ hlim
    refine new_aux₅ (- s.re) _ _ ?_ hO ?_
    · exact (asymp₂ _).natCast_atTop
    · rw [neg_sub', sub_neg_eq_add]
  · refine new_aux₄ (- (s + 1).re) r _ ?_ ?_ (by rw [← neg_re, neg_add'])
    · exact asymp₃ h₂
    · exact new_aux₆ hr hO

theorem LSeries_eq_mul_integral (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- s - 1) := by
  have h₁ := (LSeriesSummable_congr' s (modif₁ f)).mpr hS
  rw [← LSeries_congr _ (modif₀ f), LSeries_eq_mul_integral_aux (by rw [if_pos rfl]) hr hs h₁ ?_]
  · simp_rw [modif₂₀]
  · simpa only [modif₂₀] using hO

theorem LSeries_eq_mul_integral_of_nonneg (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) {r : ℝ} (hr : 0 ≤ r)
    {s : ℂ} (hs : r < s.re) (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries (fun n ↦ f n) s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, (f k : ℂ)) * t ^ (- s - 1) := by
  refine LSeries_eq_mul_integral _ hr hs ?_ ?_
  · refine LSeriesSummable_of_sum_norm_bigO (hO.congr_left fun _ ↦ ?_) hr hs
    simp_rw [norm_real, Real.norm_of_nonneg (hf _)]
  · refine (hO.congr_left fun _ ↦ ?_).of_norm_left
    rw [← ofReal_sum, norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ (hf _))]

end integral_repr

noncomputable section Residue

variable (f : ℕ → ℂ) {l : ℂ}
  (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k : ℂ) / n) atTop (𝓝 l))

section lemmas

-- Asymptotics

include hlim in
theorem key₃ : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  simp_rw [Real.rpow_one]
  refine Asymptotics.isBigO_norm_left.mp <| Asymptotics.isBigO_of_div_tendsto_nhds ?_ ‖l‖ ?_
  · filter_upwards [eventually_ne_atTop 0] with _ h using by simp [h]
  · simpa only [Function.comp_def, norm_div, norm_natCast] using (tendsto_norm.comp hlim)

end lemmas

include hlim in
theorem step1 {ε : ℝ} (hε : ε > 0) :
    ∀ᶠ t : ℝ in atTop, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t‖ < ε * t := by
  have h_lim' : Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / t) atTop (𝓝 l) := by
    refine (mul_one l ▸ ofReal_one ▸ ((hlim.comp tendsto_nat_floor_atTop).mul <|
      tendsto_ofReal_iff.mpr <| tendsto_nat_floor_div_atTop)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Function.comp_def, ofReal_div, ofReal_natCast, div_mul_div_cancel₀ (by
      rwa [Nat.cast_ne_zero, ne_eq, Nat.floor_eq_zero, not_lt])]
  rw [Metric.tendsto_nhds] at h_lim'
  filter_upwards [eventually_gt_atTop 0, h_lim' ε hε] with t ht₁ ht₂
  rwa [dist_eq_norm, div_sub' _ _ _ (ne_zero_of_re_pos ht₁), norm_div, norm_real,
    Real.norm_of_nonneg ht₁.le, mul_comm, div_lt_iff₀ ht₁] at ht₂


theorem key₁ {s : ℝ} (hs : 1 < s ) : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s) = 1 := by
  rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow, neg_div,
    mul_neg, mul_one_div, neg_div', neg_sub', sub_neg_eq_add, div_self
    (neg_add_eq_zero.not.mpr hs.ne')]

theorem key₂ {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (- s : ℂ) = 1 := by
  rw [integral_Ioi_cpow_of_lt (by rwa [neg_re, neg_lt_neg_iff]) zero_lt_one, ofReal_one, one_cpow,
    neg_div, mul_neg, mul_one_div, neg_div', neg_sub', sub_neg_eq_add, div_self]
  contrapose! hs
  rw [neg_add_eq_zero.mp hs, one_re]

theorem key₂' {s : ℝ} (hs : 1 < s) :
    (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s) = 1 := by
  rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow, neg_div,
    ← one_div_neg_eq_neg_one_div, neg_add', neg_neg, mul_one_div, div_self]
  rw [sub_ne_zero]
  exact hs.ne'

theorem key₄ {a b : ℝ} {c : ℂ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ c) (Set.Icc a b) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  exact continuous_ofReal.continuousOn.cpow_const
    (fun x hx ↦ ofReal_mem_slitPlane.mpr (ha.trans_le hx.1))

theorem key₅ {a : ℝ} {c : ℂ} (ha : 0 < a) (hc : 1 < c.re):
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (- c)) (Set.Ioi a) :=
  integrableOn_Ioi_cpow_of_lt (by rwa [neg_re, neg_lt_neg_iff]) ha

theorem key₆ {a b : ℝ} {c : ℂ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ c) (Set.Icc a b) := by
  simp_rw [mul_comm]
  exact integrableOn_mul_sum _ ha.le (key₄ ha)

include hlim in
theorem key₇ {a : ℝ} {c : ℂ} (ha : 0 < a) (hc : 1 < c.re) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (c + 1))) (Set.Ici a) := by
  refine LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun t ↦ t ^ (- c.re)) ?_ ?_ ?_
  · simp_rw [mul_comm]
    refine locallyIntegrableOn_mul_sum _ ha.le <|
      integrableOn_Ici_iff_integrableOn_Ioi.mpr (key₅ ha ?_)
    rw [add_re, one_re, lt_add_iff_pos_left]
    exact zero_lt_one.trans hc
  · refine new_aux₄ 1 (- (c + 1).re) _ ?_ ?_ ?_
    · exact new_aux₆ zero_le_one (key₃ f hlim)
    · rw [← Asymptotics.isBigO_norm_left]
      exact asymp₁ _
    · simp only [add_re, one_re, neg_add_rev, add_neg_cancel_left, le_refl]
  · refine integrableAtFilter_rpow_atTop ?_
    rwa [neg_lt_neg_iff]

theorem key₈ {T : ℝ} {c : ℂ} (hc : 1 < c.re) :
    ‖∫ (t : ℝ) in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- c - 1)‖ ≤
      ∫ (t : ℝ) in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-2 : ℂ)‖ := by
  by_cases hT : 1 < T
  · refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · rw [← neg_add']
      exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₆ _ zero_lt_one).norm
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₆ _ zero_lt_one).norm
    · have ht' : 0 < t := zero_lt_one.trans ht.1
      rw [norm_mul, norm_mul, new_aux₂ ht', new_aux₂ ht', sub_re, one_re, neg_re, neg_re, re_ofNat]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
  · rw [Set.Ioc_eq_empty hT, setIntegral_empty, setIntegral_empty, norm_zero]

theorem key₉ {T : ℝ} {c : ℂ} (hc :1 < c.re):
    ‖l * ∫ (t : ℝ) in Set.Ioc 1 T, (t : ℂ) ^ (- c)‖ ≤
      ‖l‖ * ∫ (t : ℝ) in Set.Ioc 1 T, ‖(t : ℂ) ^ (- 1 : ℂ)‖ := by
  by_cases hT : 1 < T
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₄ zero_lt_one).norm
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₄ zero_lt_one).norm
    · have ht' : 0 < t := zero_lt_one.trans ht.1
      rw [new_aux₂ ht', new_aux₂ ht', neg_re, neg_re, one_re]
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (neg_le_neg_iff.mpr hc.le)
  · rw [Set.Ioc_eq_empty hT, setIntegral_empty, setIntegral_empty, mul_zero, norm_zero, mul_zero]

theorem key₁₀ (ε : ℝ) {T : ℝ} {c : ℂ} (hT : 0 < T) (hc : 1 < c.re) :
    IntegrableOn (fun t : ℝ ↦ ‖ε * t‖ * ‖(t : ℂ) ^ (- c - 1)‖) (Set.Ioi T) := by
  simp_rw [← norm_real, ← norm_mul, ofReal_mul, mul_assoc]
  refine (((key₅ hT hc).congr ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)).const_mul _).norm
  filter_upwards with t ht
  rw [cpow_sub, cpow_one, mul_div_cancel₀]
  all_goals exact_mod_cast (hT.trans ht).ne'

theorem key₁₁ {g : ℕ → ℂ} {c : ℂ} :
     Measurable (fun t : ℝ ↦ ‖(∑ k in Icc 1 ⌊t⌋₊, g k) - c * t‖) :=
  (((by exact fun _ _ ↦ trivial : Measurable fun n : ℕ ↦ ∑ k ∈ Icc 1 n, g k).comp'
    Nat.measurable_floor).sub (by fun_prop)).norm

variable (hfS : ∀ s : ℝ, s > 1 → LSeriesSummable f s)

include hlim hfS in
theorem key_step {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, ∀ s : ℝ, 1 < s → ‖(s - 1) * LSeries f s - l * s‖ ≤ (s - 1) * s * C + s * ε := by
  obtain ⟨T₀, hT₀⟩ := (eventually_atTop).mp <| step1 f hlim hε
  let T := max 1 T₀
  have hT : 0 < T := zero_lt_one.trans_le (le_max_left _ _)
  let C₁ := ∫ t in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- 2 : ℂ)‖
  let C₂ := ‖l‖ * ∫ t in Set.Ioc 1 T, ‖(t : ℂ) ^ (- 1 : ℂ)‖
  refine ⟨C₁ + C₂, ?_, ?_⟩
  · exact add_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) <|
      mul_nonneg (norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _)
  · intro s hs
    have hs' : 0 ≤ (s - 1) * s := mul_nonneg (sub_nonneg.mpr hs.le) (zero_le_one.trans hs.le)
    have hT' : ∀ t ∈ Set.Ioi T,
        ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k - l * t‖ * ‖(t : ℂ) ^ (- (s : ℂ) - 1)‖ ≤ ‖ε * t‖ *
          ‖(t : ℂ) ^ (- (s : ℂ) - 1)‖ := fun t ht ↦ by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg hε.le (hT.trans ht).le)]
      exact (hT₀ _ (le_trans (le_max_right 1 T₀) ht.le)).le
    let C₁s := ∫ t in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)
    let C₂s := l * ∫ t in Set.Ioc 1 T, (t : ℂ) ^ (- s : ℂ)
    calc
      _ = ‖(s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ))
              - l * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (- s : ℂ))‖ := ?_
      _ = ‖(s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)) +
              (∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ))
                - l * ((∫ (t : ℝ) in Set.Ioc 1 T, (t : ℂ) ^ (- s : ℂ))
                  + (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ))))‖ := ?_
      _ = ‖(s - 1) * s * C₁s  - (s - 1) * s * C₂s +
            (s - 1) * s *
              ((∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)) -
                l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ)))‖ := by congr; ring
      _ ≤ (s - 1) * s * ‖C₁s‖ + (s - 1) * s * ‖C₂s‖ +
            (s - 1) * s *
              ‖(∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)) -
                l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ))‖ := ?_
      _ ≤ (s - 1) * s * C₁ + (s - 1) * s * C₂ +
            (s - 1) * s *
              ‖∫ (t : ℝ) in Set.Ioi T,
                (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ) - l * (t : ℂ) ^ (- s : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s *
              ‖∫ (t : ℝ) in Set.Ioi T,
                ((∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t) * (t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s *
              ∫ (t : ℝ) in Set.Ioi T,
                ‖((∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t)‖ * ‖(t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi T, ‖ε * t‖ * ‖(t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, ‖ε * t‖ * ‖(t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, ε * ‖(t : ℂ) ^ (- s : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            s * ε * ((s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s)) := ?_
      _ = (s - 1) * s * (C₁ + C₂) + s * ε := by rw [key₂' hs, mul_one]
    · rw [LSeries_eq_mul_integral _ zero_le_one (by rwa [ofReal_re]) (hfS _ hs), mul_sub,
        ← mul_assoc _ l,
        mul_rotate _ _ l, mul_assoc, mul_assoc, key₂ (by rwa [ofReal_re]), mul_one, mul_comm l]
      exact key₃ f hlim
    · rw [← Set.Ioc_union_Ioi_eq_Ioi (le_max_left 1 T₀)]
      rw [setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi, setIntegral_union
        (Set.Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi]
      · exact integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₄ zero_lt_one
      · exact key₅ hT (by rwa [ofReal_re])
      · exact integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₆ f zero_lt_one
      · rw [← neg_add']
        refine integrableOn_Ici_iff_integrableOn_Ioi.mp <| key₇ f hlim hT ?_
        rwa [ofReal_re]
    · refine le_trans (norm_add_le _ _) <| le_trans (add_le_add_right (norm_sub_le _ _) _) ?_
      rw [norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s),
        show (((s : ℂ) - 1) * s)  = ((s - 1) * s : ℝ) by rw [ofReal_mul, ofReal_sub,
          ofReal_one], Complex.norm_real, Real.norm_of_nonneg hs']
    · refine add_le_add (add_le_add ( mul_le_mul_of_nonneg_left ?_ hs')
        (mul_le_mul_of_nonneg_left ?_ hs')) ?_
      · exact key₈ _ (by rwa [ofReal_re])
      · exact key₉ (by rwa [ofReal_re])
      · rw [integral_sub, integral_mul_left]
        · rw [← neg_add']
          exact integrableOn_Ici_iff_integrableOn_Ioi.mp <| key₇ f hlim hT (by rwa [ofReal_re])
        · exact Integrable.const_mul (key₅ hT (by rwa [ofReal_re])) _
    · rw [mul_add]
      congr 3
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [sub_mul, cpow_sub, cpow_one, mul_assoc, mul_div_cancel₀]
      all_goals exact_mod_cast (hT.trans ht).ne'
    · refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ hs') _
      exact le_of_le_of_eq (norm_integral_le_integral_norm _) (by simp_rw [norm_mul])
    · refine add_le_add_left (mul_le_mul_of_nonneg_left
        (setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_) hs') _
      · refine Integrable.mono (key₁₀ ε hT (by rwa [ofReal_re])) ?_
          ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
        · refine Measurable.aestronglyMeasurable ?_
          exact key₁₁.mul (by fun_prop)
        · filter_upwards with t ht
          rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
          exact hT' t ht
      · refine key₁₀ ε hT (by rwa [ofReal_re])
      · exact hT'
    · refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ hs') _
      refine setIntegral_mono_set ?_ ?_ ?_
      · refine key₁₀ _ zero_lt_one (by rwa [ofReal_re])
      · filter_upwards with _ using mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact HasSubset.Subset.eventuallyLE <| Set.Ioi_subset_Ioi (le_max_left 1 T₀)
    · congr 2
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [norm_mul, ← norm_real t, mul_assoc, ← norm_mul, Real.norm_of_nonneg hε.le, cpow_sub,
        cpow_one, mul_div_cancel₀]
      all_goals exact ne_zero_of_one_lt_re ht
    · rw [integral_mul_left, ← mul_assoc, ← mul_assoc, ← mul_rotate _ s]
      congr 2
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [new_aux₂ (zero_lt_one.trans ht), neg_re, ofReal_re]

include hlim hfS in
theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := by
  refine Metric.tendsto_nhdsWithin_nhds.mpr fun ε hε ↦ ?_
  have hε6 : 0 < ε / 6 := by positivity
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨C, hC₁, hC₂⟩ := key_step f hlim hfS hε6
  have lim1 : Tendsto (fun s ↦ (s - 1) * s * C) (𝓝[>] 1) (𝓝 0) := by
    have : ContinuousAt (fun s ↦ (s - 1) * s * C) 1 := by fun_prop
    convert tendsto_nhdsWithin_of_tendsto_nhds this.tendsto
    rw [sub_self, zero_mul, zero_mul]
  have lim2 : Tendsto (fun s : ℝ ↦ s * l) (𝓝[>] 1) (𝓝 l) := by
    have : ContinuousAt (fun s : ℝ ↦ s * l) 1 := by fun_prop
    convert tendsto_nhdsWithin_of_tendsto_nhds this.tendsto
    rw [Complex.ofReal_one, one_mul]
  rw [Metric.tendsto_nhdsWithin_nhds] at lim1 lim2
  obtain ⟨δ₁, _, hδ₁⟩ := lim1 _ hε3
  obtain ⟨δ₂, _, hδ₂⟩ := lim2 _ hε3
  refine ⟨min 1 (min δ₁ δ₂), by positivity, fun s hs₁ hs₂ ↦ ?_⟩
  specialize hC₂ s hs₁
  specialize hδ₁ hs₁ <| hs₂.trans_le <| (min_le_right _ _).trans (min_le_left _ _)
  specialize hδ₂ hs₁ <| hs₂.trans_le <| (min_le_right _ _).trans (min_le_right _ _)
  rw [dist_eq_norm] at hδ₁ hδ₂ hs₂ ⊢
  rw [sub_zero, Real.norm_of_nonneg (mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hs₁.le) (zero_lt_one.trans hs₁).le) hC₁)] at hδ₁
  have sle2 : s < 2 := by
    have := (abs_lt.mp <| Real.norm_eq_abs _ ▸ (hs₂.trans_le (min_le_left _ _))).2
    rwa [sub_lt_iff_lt_add', one_add_one_eq_two] at this
  calc
    _ ≤ ‖(s - 1) * LSeries f s - l * s‖ + ‖l * s - l‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < (s - 1) * s * C + s * (ε / 6) + (ε / 3) := add_lt_add_of_le_of_lt hC₂ (by rwa [mul_comm])
    _ ≤ (ε / 3) + s * (ε / 6) + (ε / 3) := by gcongr
    _ < (ε / 3) + (ε / 3) + (ε / 3) := ?_
    _ = ε := add_thirds ε
  refine add_lt_add_right (add_lt_add_left ?_ (ε / 3)) (ε / 3)
  exact lt_of_lt_of_eq ((mul_lt_mul_right hε6).mpr sle2) (by ring)

theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg (f : ℕ → ℝ) {l : ℝ}
    (hf : Tendsto (fun n ↦ (∑ k ∈ Icc 1 n, f k) / (n : ℝ)) atTop (𝓝 l))
    (hf' : ∀ n, 0 ≤ f n) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (fun n ↦ f n) s) (𝓝[>] 1) (𝓝 l) := by
  refine  LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div (fun n ↦ f n)
    (hf.ofReal.congr fun _ ↦ ?_)
    fun s hs ↦ LSeriesSummable_of_sum_norm_bigO (f := fun n ↦ f n) ?_ zero_le_one
      (by rwa [ofReal_re])
  · simp only [ofReal_div, ofReal_sum, ofReal_natCast]
  · convert Asymptotics.IsBigO.norm_left <| key₃ (fun n ↦ f n) ?_ (l := l)
    · rw [← ofReal_sum, norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ hf' _)]
      simp_rw [norm_real, Real.norm_of_nonneg (hf' _)]
    · simp_rw [← ofReal_sum, ← ofReal_natCast, ← ofReal_div]
      exact tendsto_ofReal_iff.mpr hf
