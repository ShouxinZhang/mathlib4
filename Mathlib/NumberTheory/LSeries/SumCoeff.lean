/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
  # Docs
-/


section

open Asymptotics Filter

theorem Asymptotics.isEquivalent_nat_floor {R : Type*} [NormedLinearOrderedField R]
    [OrderTopology R] [FloorRing R] :
    (fun (x : R) ↦ ↑⌊x⌋₊) ~[atTop] (fun x ↦ x) := by
  refine isEquivalent_of_tendsto_one ?_ ?_
  · filter_upwards with x hx
    rw [hx, Nat.floor_zero, Nat.cast_eq_zero]
  · exact tendsto_nat_floor_div_atTop

theorem Asymptotics.isEquivalent_nat_ceil {R : Type*} [NormedLinearOrderedField R]
    [OrderTopology R] [FloorRing R] :
    (fun (x : R) ↦ ↑⌈x⌉₊) ~[atTop] (fun x ↦ x) := by
  refine isEquivalent_of_tendsto_one ?_ ?_
  · filter_upwards with x hx
    rw [hx, Nat.ceil_zero, Nat.cast_eq_zero]
  · exact tendsto_nat_ceil_div_atTop

end

open Finset Filter MeasureTheory Topology Complex

private theorem aux1 {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (deriv fun (t : ℝ) ↦ (t : ℂ) ^ (-s)) (Set.Ici 1) := by
  have h_int : IntegrableOn (fun x ↦ Complex.abs (-s) * x ^ (-s - 1).re) (Set.Ici 1) := by
    refine Integrable.const_mul (integrableOn_Ici_iff_integrableOn_Ioi.mpr
      ((integrableOn_Ioi_rpow_iff zero_lt_one).mpr ?_)) _
    rwa [sub_re, neg_re, one_re, sub_lt_iff_lt_add, neg_add_cancel, neg_lt_zero]
  refine (integrable_norm_iff (aestronglyMeasurable_deriv _ _)).mp <|
    h_int.congr_fun (fun t ht ↦ ?_) measurableSet_Ici
  rw [norm_eq_abs, deriv_cpow_const' (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr
    (ne_zero_of_re_pos hs)), map_mul, abs_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ht)]

private theorem aux2 (f : ℕ → ℂ) (hf₀ : f 0 = 0) (s : ℂ) (n : ℕ) :
    ∑ k in range (n + 1), LSeries.term f s k = ∑ k ∈ Icc 0 n, ↑k ^ (- s) * f k := by
  rw [← Nat.Ico_zero_eq_range, Nat.Ico_succ_right]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  obtain hk | rfl := ne_or_eq k 0
  · rw [LSeries.term_of_ne_zero hk, Complex.cpow_neg, mul_comm, div_eq_mul_inv]
  · rw [LSeries.term_zero, hf₀, mul_zero]

private theorem aux3 {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hbO : (fun n ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun t : ℝ ↦ ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =O[atTop] fun t : ℝ ↦ t ^ r := by
  refine (Asymptotics.IsBigO.comp_tendsto hbO tendsto_nat_floor_atTop).trans <|
    (Asymptotics.isEquivalent_nat_floor).isBigO.rpow hr ?_
  filter_upwards [eventually_ge_atTop 0] with _ ht using ht

private theorem aux4 {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → 𝕜} {g : ℕ → 𝕜} (r : ℝ) (s : ℂ)
    (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ s.re)
    (hf : (fun n ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun n ↦ g n * ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ (s.re + r) := by
  refine Asymptotics.IsBigO.congr' (hg.mul hf) EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with _ h using by rw [← Real.rpow_add (Nat.cast_pos.mpr h)]

private theorem aux4' {𝕜 : Type*} [RCLike 𝕜]
    {f : ℕ → 𝕜} {g : ℝ → 𝕜} {r : ℝ} (s : ℂ) (hr : 0 ≤ r)
    (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ s.re)
    (hf : (fun n ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun t : ℝ ↦ g t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =O[atTop] fun t ↦ (t : ℝ) ^ (s.re + r) := by
  refine Asymptotics.IsBigO.congr' (hg.mul (aux3 hr hf)) EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with _ h using by rw [← Real.rpow_add h]

theorem integral_repr (f : ℕ → ℂ)
    {r : ℝ} (hr : 0 ≤ r)
    (s : ℂ)
    (hs : r < s.re)
    (hLS : LSeriesSummable f s)
    (hbO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- s - 1) := by
  let g : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f n
  have h_fg : ∀ {n : ℕ}, n ≠ 0 → f n = g n := fun h ↦ by simp only [g, if_neg h]
  have h_g₀ : g 0 = 0 := by simp only [reduceIte, g]
  have h_sum : ∀ n, ∑ k ∈ Icc 0 n, g k = ∑ k ∈ Icc 1 n, f k := by
    intro n
    rw [← Nat.Icc_insert_succ_left n.zero_le, sum_insert, h_g₀, zero_add, zero_add,
      sum_congr rfl (fun _ h ↦ by rw [← h_fg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne'])]
    simp only [mem_Icc, not_and, zero_add, nonpos_iff_eq_zero, one_ne_zero, false_implies]
  simp_rw [← h_sum] at hbO
  have h_lim : Tendsto (fun n : ℕ ↦ (n : ℂ) ^ (-s) * ∑ k ∈ Icc 0 n, g k)
      Filter.atTop (nhds 0) := by
    refine Asymptotics.IsBigO.trans_tendsto ?_ <|
      (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp tendsto_natCast_atTop_atTop
    simp_rw [Function.comp_def, neg_sub', sub_neg_eq_add]
    refine aux4 r (- s) ?_ hbO
    simp_rw [← abs_natCast]
    refine (Complex.isTheta_cpow_const_rpow (f := fun n : ℕ ↦ (n : ℂ)) ?_).1
    exact fun h ↦ False.elim <| Complex.re_neg_ne_zero_of_re_pos (hr.trans_lt hs) <| h
  have h_int : IntegrableAtFilter (fun x : ℝ ↦ x ^ ((- s - 1).re + r)) atTop :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by
        rwa [← lt_neg_add_iff_add_lt, ← neg_re, neg_sub, sub_neg_eq_add, add_re, one_re,
          add_neg_cancel_comm])⟩
  rw [LSeries_congr s h_fg, ← integral_mul_left]
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).mpr
    ((LSeriesSummable_congr s h_fg).mp hLS).hasSum.tendsto_sum_nat) ?_
  simp_rw [aux2 _ h_g₀]
  convert tendsto_sum_mul_atTop_eq_sub_integral₀ g h_g₀ ?_ (aux1 (hr.trans_lt hs)) h_lim ?_ h_int
  · rw [zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp_rw [h_sum, Complex.deriv_cpow_const' (zero_lt_one.trans ht).ne'
      (neg_ne_zero.mpr <| Complex.ne_zero_of_re_pos (hr.trans_lt hs))]
    ring
  · intro t ht
    exact differentiableAt_id'.cpow_const' (zero_lt_one.trans_le ht).ne'
      (neg_ne_zero.mpr <| Complex.ne_zero_of_re_pos (hr.trans_lt hs))
  · refine aux4' (f := g) (s := - s - 1)
      (g := fun t : ℝ ↦ deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) t) ?_ ?_ hbO
    · exact hr
    · rw [sub_re, one_re]
      exact isBigO_deriv_cpow_const_atTop (- s)

example (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Set.Ioi (1 : ℝ), ⌊t⌋₊ / (t : ℂ) ^ (s + 1) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  rw [integral_repr _ zero_le_one s hs (LSeriesSummable_one_iff.mpr hs)]
  · rw [mul_right_inj' (Complex.ne_zero_of_one_lt_re hs)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp_rw [Pi.one_apply, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one,
      div_eq_mul_inv, ← Complex.cpow_neg, neg_add']
  · simp_rw [Real.rpow_one]
    refine Eventually.isBigO ?_
    filter_upwards with n using by simp

theorem summable_of_abel (f : ℕ → ℂ)
    {r : ℝ} (hr : 0 ≤ r)
    (hbO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (s : ℂ)
    (hs : r < s.re)
    :
    LSeriesSummable f s := by
  let g : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f n
  have h_fg : ∀ {n : ℕ}, n ≠ 0 → f n = g n := fun h ↦ by simp only [g, if_neg h]
  have h_g₀ : g 0 = 0 := by simp only [g, reduceIte]
  have h_sum : ∀ n, ∑ k ∈ Icc 0 n, ‖g k‖ = ∑ k ∈ Icc 1 n, ‖f k‖ := by
    intro n
    rw [← Nat.Icc_insert_succ_left n.zero_le, sum_insert, h_g₀, zero_add, norm_zero, zero_add,
      sum_congr rfl (fun _ h ↦ by rw [← h_fg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne'])]
    simp only [mem_Icc, not_and, zero_add, nonpos_iff_eq_zero, one_ne_zero, false_implies]
  simp_rw [← h_sum] at hbO
  have h_int : IntegrableAtFilter (fun x : ℝ ↦ x ^ ((- s - 1).re + r)) atTop :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by
        rwa [← lt_neg_add_iff_add_lt, ← neg_re, neg_sub, sub_neg_eq_add, add_re, one_re,
          add_neg_cancel_comm])⟩
  have h_seq : Set.EqOn (deriv fun t : ℝ ↦ t ^ (-s.re))
      (deriv fun t ↦ ‖(fun t : ℝ ↦ (t : ℂ) ^ (-s)) t‖) (Set.Ici 1) := by
    intro t ht
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [eventually_gt_nhds (zero_lt_one.trans_le ht)] with x hx
    rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hx, neg_re]
  rw [LSeriesSummable_congr s h_fg]
  refine Summable.congr_atTop (f₁ := fun n ↦ (n : ℂ) ^ (-s) * (g n)) ?_ ?_
  · refine summable_mul_of_bigO_atTop₀ g ?_ (f := fun t ↦ (t : ℂ) ^ (-s))
      ?_ ?_ ?_ ?_ h_int
    · exact h_g₀
    · intro t ht
      · refine DifferentiableAt.norm ℂ ?_ ?_
        · refine DifferentiableAt.cpow_const' ?_ ?_ ?_
          · exact differentiableAt_id
          · exact (zero_lt_one.trans_le ht).ne'
          · exact (neg_ne_zero.mpr <| Complex.ne_zero_of_re_pos (hr.trans_lt hs))
        refine (Complex.cpow_ne_zero ?_).mpr ?_
        · exact (neg_ne_zero.mpr <| Complex.ne_zero_of_re_pos (hr.trans_lt hs))
        · exact_mod_cast (zero_lt_one.trans_le ht).ne'
    · refine IntegrableOn.congr_fun ?_ h_seq measurableSet_Ici
      refine IntegrableOn.congr_fun ?_
        (fun t ht ↦ by
          rw [Real.deriv_rpow_const]
          left
          exact (zero_lt_one.trans_le ht).ne') measurableSet_Ici
      refine Integrable.const_mul (integrableOn_Ici_iff_integrableOn_Ioi.mpr
        ((integrableOn_Ioi_rpow_iff zero_lt_one).mpr ?_)) _
      rw [sub_lt_iff_lt_add, neg_add_cancel, neg_lt_zero]
      exact hr.trans_lt hs
    · have := aux4 r (- r) (f := fun n ↦ ‖g n‖) (g := fun n ↦ ‖(n : ℂ) ^ (-s)‖) ?_ ?_
      · simp_rw [neg_re, ofReal_re, neg_add_cancel, Real.rpow_zero] at this
        exact this
      · refine Eventually.isBigO ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        rw [norm_norm, Complex.norm_natCast_cpow_of_re_ne_zero, neg_re, neg_re, ofReal_re]
        · refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
          · exact_mod_cast hn
          · rw [neg_le_neg_iff]
            exact hs.le
        refine re_neg_ne_zero_of_re_pos ?_
        exact hr.trans_lt hs
      exact hbO
    · refine aux4' _ hr ?_ ?_
      · have : (deriv fun t : ℝ ↦ t ^ (-s.re)) =ᶠ[atTop]
            (deriv fun t ↦ ‖(fun t : ℝ ↦ (t : ℂ) ^ (-s)) t‖) := by
          filter_upwards [eventually_ge_atTop 1] with t ht using h_seq ht
        refine Asymptotics.IsBigO.congr' ?_ this EventuallyEq.rfl
        rw [sub_re, one_re]
        exact isBigO_deriv_rpow_const_atTop (- s.re)
      exact hbO
  · filter_upwards [eventually_ne_atTop 0] with n hn
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, Complex.cpow_neg, mul_comm]

variable (f : ℕ → ℂ) (l : ℂ)
  (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k : ℂ) / n) atTop (𝓝 l))

include hlim

theorem lemma0 {ε : ℝ} (hε : ε > 0) :
    ∀ᶠ t : ℝ in atTop, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t‖ < ε * t := by
  have h_lim' : Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / t) atTop (𝓝 l) := by
    have lim1 : Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / ⌊t⌋₊) atTop (𝓝 l) :=
      Tendsto.comp hlim (tendsto_nat_floor_atTop (α := ℝ))
    have lim2 : Tendsto (fun t : ℝ ↦ ↑(⌊t⌋₊ / t : ℝ)) atTop (𝓝 (1 : ℂ)) := by
      rw [← Complex.ofReal_one]
      rw [tendsto_ofReal_iff]
      exact tendsto_nat_floor_div_atTop
    have lim3 := Tendsto.mul lim1 lim2
    rw [mul_one] at lim3
    refine Tendsto.congr' ?_ lim3
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Complex.ofReal_div, Complex.ofReal_natCast, div_mul_div_cancel₀]
    rw [Nat.cast_ne_zero, ne_eq, Nat.floor_eq_zero, not_lt]
    exact ht
  rw [Metric.tendsto_nhds] at h_lim'
  specialize h_lim' ε hε
  filter_upwards [eventually_gt_atTop 0, h_lim'] with t ht₁ ht₂
  rwa [← div_lt_iff₀, ← Real.norm_of_nonneg (r := t), ← Complex.norm_real, ← norm_div,
    Complex.norm_real, Real.norm_of_nonneg (r := t), sub_div, mul_div_cancel_right₀]
  · exact_mod_cast ht₁.ne'
  · exact ht₁.le
  · exact ht₁.le
  · exact ht₁

theorem lemma1 :
    (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  simp_rw [Real.rpow_one]
  rw [← Asymptotics.isBigO_norm_left]
  refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ ‖l‖ ?_
  · filter_upwards [eventually_ne_atTop 0] with _ h using
      fun h' ↦ False.elim <| h (Nat.cast_eq_zero.mp h')
  · simpa only [Function.comp_def, norm_div, norm_natCast] using (tendsto_norm.comp hlim)

theorem lemmaI {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, ∀ s : ℝ, 1 < s → ‖(s - 1) * LSeries f s - l * s‖ ≤ (s - 1) * s * C + s * ε := by
  obtain ⟨T₀, hT₀⟩ := (eventually_atTop).mp <| lemma0 f l hlim hε
  let T := max 1 T₀
  have hT : ∀ t ≥ T, ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k - l * t‖ ≤ ε * t :=
    fun _ h ↦ (hT₀  _ <| (le_max_right _ _).trans h).le
  let C₁ := ∫ t in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- 2 : ℂ)‖
  let C₂ := ‖l‖ * ∫ t in Set.Ioc 1 T, ‖(t : ℂ) ^ (- 1 : ℂ)‖
  use C₁ + C₂
  refine ⟨sorry, ?_⟩
  intro s hs
  have hs' : 0 ≤ (s - 1) * s := mul_nonneg (sub_nonneg.mpr hs.le) (zero_le_one.trans hs.le)
  let C₁s := ∫ t in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)
  let C₂s := l * ∫ t in Set.Ioc 1 T, (t : ℂ) ^ (- s : ℂ)
  have h_intOn₁ : ∀ ⦃a b : ℝ⦄ ⦃c : ℂ⦄, 0 < a →
      IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ c) (Set.Ioc a b) :=
    fun _ _ _ h ↦ integrableOn_Icc_iff_integrableOn_Ioc.mp <|
      (continuous_ofReal.continuousOn.cpow_const
        fun x hx ↦ ofReal_mem_slitPlane.mpr (h.trans_le hx.1)).integrableOn_compact isCompact_Icc
  have h_intOn₂ : ∀ ⦃a : ℝ⦄ ⦃c : ℂ⦄, IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ c) (Set.Ioi a) := by
    intro _ _
    rw [integrableOn_Ioi_cpow_iff]

  have hC₁ : ‖C₁s‖ ≤ C₁ := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · refine Integrable.norm ?_
      sorry
    · refine Integrable.norm ?_
      sorry
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    sorry
  have hC₂ : ‖C₂s‖ ≤ C₂ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · refine Integrable.norm (h_intOn₁ zero_lt_one)
    · refine Integrable.norm (h_intOn₁ zero_lt_one)
    · sorry
  have h_int : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s) = 1 := by
    rw [integral_Ioi_rpow_of_lt _ zero_lt_one, Real.one_rpow, neg_div, mul_neg, mul_one_div,
      neg_div', neg_sub', sub_neg_eq_add, div_self]
    · exact neg_add_eq_zero.not.mpr hs.ne'
    · exact neg_lt_neg_iff.mpr hs
  have h_int' : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (- s : ℂ) = 1 := by
    rw [integral_Ioi_cpow_of_lt _ zero_lt_one, Complex.ofReal_one, Complex.one_cpow, neg_div,
      mul_neg, mul_one_div, neg_div', neg_sub', sub_neg_eq_add, div_self]
    · exact neg_add_eq_zero.not.mpr <| ofReal_ne_one.mpr hs.ne'
    · rwa [neg_re, ofReal_re, neg_lt_neg_iff]
  have h_Iio₁ : Set.Ioi 1 = Set.Ioc 1 T ∪ Set.Ioi T := by
    rw [Set.Ioc_union_Ioi_eq_Ioi (le_max_left 1 T₀)]
  have h_Iio₂ : Disjoint (Set.Ioc 1 T) (Set.Ioi T) := Set.Ioc_disjoint_Ioi le_rfl
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
              l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ)))‖ := ?_
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
    _ = (s - 1) * s * (C₁ + C₂) +
          (s - 1) * s * ∫ (t : ℝ) in Set.Ioi T, ε * ‖(t : ℂ) ^ (- s : ℂ)‖ := ?_
    _ ≤ (s - 1) * s * (C₁ + C₂) +
          (s - 1) * s * ε * ∫ (t : ℝ) in Set.Ioi 1, ‖(t : ℂ) ^ (- s : ℂ)‖ := ?_
    _ = (s - 1) * s * (C₁ + C₂) +
          s * ε * (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s) := ?_
    _ = (s - 1) * s * (C₁ + C₂) + s * ε := ?_
  · rw [integral_repr _ zero_le_one, mul_sub, ← mul_assoc _ l, mul_rotate _ _ l,
      mul_assoc, mul_assoc, h_int', mul_one, mul_comm l]
    · rwa [ofReal_re]
    · convert summable_of_abel f zero_le_one ?_ ?_ ?_
      · sorry
      · sorry
    · exact lemma1 f l hlim
  · rw [h_Iio₁, setIntegral_union h_Iio₂ measurableSet_Ioi, setIntegral_union h_Iio₂
      measurableSet_Ioi]
    · refine Continuous.integrableOn_Ioc ?_
      refine continuous_ofReal_cpow_const ?_
      sorry
    · rw [integrableOn_Ioi_cpow_iff]
      · sorry
      · sorry
    · sorry
    · sorry
  · congr 1
    ring
  · refine le_trans (norm_add_le _ _) <| le_trans (add_le_add_right (norm_sub_le _ _) _) ?_
    rw [norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s)]
    rw [show (((s : ℂ) - 1) * s)  = ((s - 1) * s : ℝ) by rw [ofReal_mul, ofReal_sub,
      ofReal_one], Complex.norm_real, Real.norm_of_nonneg hs']
  · refine add_le_add (add_le_add ?_ ?_) ?_
    · exact mul_le_mul_of_nonneg_left hC₁ hs'
    · exact mul_le_mul_of_nonneg_left hC₂ hs'
    · rw [integral_sub, integral_mul_left]
      · sorry
      · refine Integrable.const_mul ?_ _
        rw [← IntegrableOn, integrableOn_Ioi_cpow_iff]
        · sorry
        · sorry
  · rw [mul_add]
    congr 3
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have : (t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr <| (zero_lt_one.trans ((le_max_left 1 T₀).trans_lt ht)).ne'
    rw [sub_mul, Complex.cpow_sub _ _ this, Complex.cpow_one, mul_assoc, mul_div_cancel₀ _ this]
  · refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ hs') _
    exact le_of_le_of_eq (norm_integral_le_integral_norm _) (by simp_rw [norm_mul])
  · refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ hs') _
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
    · sorry -- painful
    · sorry -- painful
    · intro t ht
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_of_nonneg]
      · exact hT _ ht.le
      refine mul_nonneg ?_ ?_
      · exact hε.le
      · exact zero_le_one.trans ((le_max_left 1 T₀).trans ht.le)
  · congr 2
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have : (t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr <| (zero_lt_one.trans ((le_max_left 1 T₀).trans_lt ht)).ne'
    rw [norm_mul, Real.norm_of_nonneg hε.le, ← Complex.norm_real, mul_assoc, ← norm_mul,
      Complex.cpow_sub _ _ this, Complex.cpow_one, mul_div_cancel₀ _ this]
  · rw [integral_mul_left, ← mul_assoc]
    refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hs' hε.le)) _
    refine setIntegral_mono_set ?_ ?_ ?_
    · refine Integrable.norm ?_
      rw [← IntegrableOn, integrableOn_Ioi_cpow_iff]
      · sorry
      · sorry
    · filter_upwards with _ using norm_nonneg _
    · exact HasSubset.Subset.eventuallyLE <| Set.Ioi_subset_Ioi (le_max_left 1 T₀)
  · congr 2
    · ring
    · refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow (zero_le_one.trans ht.le), Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans ht.le) _)]
  · rw [mul_assoc _ (s - 1), h_int, mul_one]




#exit
    congr 1

    ring_nf
    congr

    -- congr
    -- ring
#exit
  · refine le_of_le_of_eq (norm_add_le _ _) ?_
    rw [show ((s : ℂ) - 1) * ↑s = ↑((s - 1) * s) by simp only [ofReal_mul,
        ofReal_sub, ofReal_one], norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg]
    sorry
  · rw [integral_sub, integral_mul_left]
    · sorry
    · sorry
  · congr 3
    refine setIntegral_congr_fun ?_ ?_
    · sorry
    · intro t ht
      dsimp only
      rw [sub_mul, Complex.cpow_sub, Complex.cpow_one, mul_assoc, mul_div_cancel₀]
      · sorry
      · sorry
  · refine add_le_add_left ?_ _
    refine mul_le_mul_of_nonneg_left ?_ ?_

    · refine le_of_le_of_eq (norm_integral_le_integral_norm _) ?_
      simp_rw [norm_mul]
    · sorry
  ·
    refine add_le_add_left ?_ _
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · refine setIntegral_mono_on ?_ ?_ ?_ ?_
      · sorry
      · sorry
      · sorry
      · intro t ht
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · rw [Real.norm_of_nonneg]
          · apply hT
            exact ht.le
          · sorry
        exact norm_nonneg _
    sorry
  · congr 2
    refine setIntegral_congr_fun ?_ ?_
    · sorry
    · intro t ht
      dsimp only
      rw [norm_mul, Real.norm_of_nonneg hε.le, mul_assoc, ← Complex.norm_real, ← norm_mul,
        Complex.cpow_sub, Complex.cpow_one, mul_div_cancel₀]
      · sorry
      · sorry
  · rw [integral_mul_left, ← mul_assoc]
    refine add_le_add_left ?_ _
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · refine setIntegral_mono_set ?_ ?_ ?_
      · sorry
      · filter_upwards with _ using norm_nonneg _
      · refine HasSubset.Subset.eventuallyLE ?_
        refine Set.Ioi_subset_Ioi ?_
        sorry
    · sorry
  · congr 2
    · ring
    · refine setIntegral_congr_fun ?_ ?_
      · sorry
      · intro t ht
        dsimp only
        rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow, Complex.norm_real, Real.norm_of_nonneg]
        · sorry
        · sorry
  · rw [mul_assoc, mul_assoc, h_int, mul_one]

theorem final : Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε6 : 0 < ε / 6 := by positivity
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨C, hC₁, hC₂⟩ := lemmaI f l hlim hε6
  have lim1 : Tendsto (fun s ↦ (s - 1) * s * C) (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have : ContinuousAt (fun s ↦ (s - 1) * s * C) 1 := by fun_prop
    have := this.tendsto
    rwa [sub_self, zero_mul, zero_mul] at this
  have lim2 : Tendsto (fun s : ℝ ↦ s * l) (𝓝[>] 1) (𝓝 l) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have : ContinuousAt (fun s : ℝ ↦ s * l) 1 := by fun_prop
    have := this.tendsto
    rwa [Complex.ofReal_one, one_mul] at this
  rw [Metric.tendsto_nhdsWithin_nhds] at lim1 lim2
  obtain ⟨δ₁, _, hδ₁⟩ := lim1 _ hε3
  obtain ⟨δ₂, _, hδ₂⟩ := lim2 _ hε3
  use min 1 (min δ₁ δ₂)
  refine ⟨by positivity, ?_⟩
  intro s hs₁ hs₂
  specialize hC₂ s hs₁
  specialize hδ₁ hs₁ <| hs₂.trans_le <| (min_le_right _ _).trans (min_le_left _ _)
  specialize hδ₂ hs₁ <| hs₂.trans_le <| (min_le_right _ _).trans (min_le_right _ _)
  rw [dist_eq_norm] at hδ₁ hδ₂ hs₂ ⊢
  rw [sub_zero, Real.norm_of_nonneg (mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hs₁.le) (zero_lt_one.trans hs₁).le) hC₁)] at hδ₁
  calc
    _ ≤ ‖(s - 1) * LSeries f s - l * s‖ + ‖l * s - l‖ := ?_
    _ < (s - 1) * s * C + s * (ε / 6) + (ε / 3) := ?_
    _ < (ε / 3) + (ε / 3) + (ε / 3) := ?_
    _ = ε := ?_
  · exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  · refine add_lt_add hC₂ ?_
    rwa [mul_comm]
  · refine (add_lt_add_iff_right _).mpr ?_
    refine add_lt_add ?_ ?_
    · exact hδ₁
    · have : s < 2 := by
        have := hs₂.trans_le (min_le_left _ _)
        rw [Real.norm_eq_abs, abs_lt, sub_lt_iff_lt_add', one_add_one_eq_two] at this
        exact this.2
      have := (mul_lt_mul_right hε6).mpr this
      rwa [show 2 * (ε / 6) = ε / 3 by ring] at this
  · exact add_thirds ε

#exit



variable (f : ℕ → ℂ) (l : ℂ)
  (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k : ℂ) / n) atTop (𝓝 l))

include hlim

theorem lemma1 :
    Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / t) atTop (𝓝 l) := by
  have lim1 : Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / ⌊t⌋₊) atTop (𝓝 l) :=
    Tendsto.comp hlim (tendsto_nat_floor_atTop (α := ℝ))
  have lim2 : Tendsto (fun t : ℝ ↦ ↑(⌊t⌋₊ / t : ℝ)) atTop (𝓝 (1 : ℂ)) := by
    rw [← Complex.ofReal_one]
    rw [tendsto_ofReal_iff]
    exact tendsto_nat_floor_div_atTop
  have lim3 := Tendsto.mul lim1 lim2
  rw [mul_one] at lim3
  refine Tendsto.congr' ?_ lim3
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [Complex.ofReal_div, Complex.ofReal_natCast, div_mul_div_cancel₀]
  rw [Nat.cast_ne_zero, ne_eq, Nat.floor_eq_zero, not_lt]
  exact ht

theorem assume1 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k - l * t‖ < ε * t := by
  have := lemma1 f l hlim
  rw [Metric.tendsto_nhds] at this
  specialize this ε hε
  filter_upwards [eventually_gt_atTop 0, this] with t ht₁ ht₂
  rwa [← div_lt_iff₀, ← Real.norm_of_nonneg (r := t), ← Complex.norm_real, ← norm_div,
    Complex.norm_real, Real.norm_of_nonneg (r := t), sub_div, mul_div_cancel_right₀]
  · exact_mod_cast ht₁.ne'
  · exact ht₁.le
  · exact ht₁.le
  · exact ht₁

theorem final_step1 (hf : f 0 = 0) (ε : ℝ) (hε : 0 < ε) :
   -- maybe state as ‖(LSeries f s) / s - l / (s - 1)‖ ≤ C + ε / (s - 1)
    ∃ C, ∀ s : ℝ, 1 < s → ‖(LSeries f s) / s - l / (s - 1)‖ ≤ C + ε / (s - 1) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp <| assume1 f l hlim hε
  -- need : 1 < T
  let C := ∫ t in Set.Ioc 1 T, ‖((∑ k ∈ Icc 0 ⌊t⌋₊, f k) - l * t) / (t : ℂ) ^ (1 + 1 : ℂ)‖
--  let C₁ := ε * ∫ t in Set.Ioc 1 T, t⁻¹
  use C
  intro s hs
  calc
    _ = ‖∫ t in Set.Ioi (1 : ℝ), ((∑ k ∈ Icc 0 ⌊t⌋₊, f k) - l * t) / (t : ℂ) ^ (s + 1 : ℂ)‖ := ?_
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), ‖((∑ k ∈ Icc 0 ⌊t⌋₊, f k) - l * t) / (t : ℂ) ^ (s + 1 : ℂ)‖ := ?_
    _ = (∫ t in Set.Ioc 1 T, ‖((∑ k ∈ Icc 0 ⌊t⌋₊, f k) - l * t) / (t : ℂ) ^ (s + 1 : ℂ)‖)
      + ∫ t in Set.Ioi T, ‖((∑ k ∈ Icc 0 ⌊t⌋₊, f k) - l * t) / (t : ℂ) ^ (s + 1 : ℂ)‖ := ?_
    _ ≤ C + ∫ t in Set.Ioi T, ‖ε * t / (t : ℂ) ^ (s + 1 : ℂ)‖ := ?_
    _ = C + ∫ t in Set.Ioi T, ε * t / t ^ (s + 1) := ?_
    _ = C + ε * ∫ t in Set.Ioi T, t ^ (- s) := ?_
    _ ≤ C + ε * ∫ t in Set.Ioi 1, t ^ (- s) := ?_
    _ = C + ε /(s - 1) := ?_
  · rw [integral_repr]
    · sorry
    · exact 1
    · sorry
    · sorry
    · sorry
    · sorry
  · exact norm_integral_le_integral_norm _
  · rw [show Set.Ioi 1 = Set.Ioc 1 T ∪ Set.Ioi T by sorry]
    rw [setIntegral_union]
    · sorry
    · sorry
    · sorry
    · sorry
  · gcongr
    · sorry
    · sorry
    · sorry
    · sorry
  · rw [add_left_cancel_iff]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    rw [show (s : ℂ) + 1 = (s + 1 : ℝ) by sorry, ← Complex.ofReal_cpow, ← Complex.ofReal_mul,
      ← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg]
    · sorry
    · sorry
  · simp_rw [mul_div_assoc]
    rw [integral_mul_left]
    rw [add_left_cancel_iff, mul_left_cancel_iff_of_pos hε]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have : x ≠ 0 := sorry
    rw [Real.rpow_add_one, Real.rpow_neg]
    · exact div_mul_cancel_right₀ this _
    · sorry
    · exact this
  · gcongr
    refine setIntegral_mono_set ?_ ?_ ?_
    · sorry
    · sorry
    · refine HasSubset.Subset.eventuallyLE ?_
      refine Set.Ioi_subset_Ioi ?_
      sorry
  · rw [add_left_cancel_iff, ← mul_one_div, mul_left_cancel_iff_of_pos hε]
    rw [integral_Ioi_rpow_of_lt, Real.one_rpow, neg_div, ← div_neg, neg_add', neg_neg]
    · sorry
    · sorry

theorem final_step2 (hf : f 0 = 0) :
    Tendsto (fun s : ℝ ↦ ‖s * (s - 1) * LSeries f s - s * l‖) (𝓝[>] 1) (𝓝 0) := by
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  have h1 := final_step1 f l hlim hf ε hε
  sorry

theorem final : Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := by
  have hlim : Tendsto (fun s : ℝ ↦ ‖s * (s - 1) * LSeries f s - s * l‖) (𝓝[>] 1) (𝓝 0) := sorry
  rw [← tendsto_zero_iff_norm_tendsto_zero] at hlim
  rw [NormedAddCommGroup.tendsto_nhds_zero] at hlim
  rw [Metric.tendsto_nhds]
  intro ε hε
  specialize hlim ε sorry
  filter_upwards [hlim, eventually_mem_nhdsWithin] with x hx₁ hx₂
  rw [mul_assoc, ← mul_sub, norm_mul, ← lt_div_iff₀'] at hx₁
  · refine lt_trans hx₁ ?_
    refine div_lt_self ?_ ?_
    · exact hε
    · sorry
  · sorry
