/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.ComplexMGF

/-!
# The moment generating function is analytic

The moment generating function is analytic on the interior of the interval on which it is defined.

## Main results

TODO

-/


open MeasureTheory Filter Finset Real

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

-- found on zulip
theorem Real.exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' n, x^n / n.factorial := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

lemma _root_.Summable.mono {β E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f g : β → E} (hg : Summable g)
    (hfg : ∀ b, ‖f b‖ ≤ ‖g b‖) :
    Summable f := by
  rw [← summable_norm_iff] at hg ⊢
  refine summable_of_sum_le (c := ∑' x, ‖g x‖) (fun _ ↦ by positivity) (fun s ↦ ?_)
  exact (sum_le_sum fun i _ ↦ hfg i).trans (sum_le_tsum s (fun _ _ ↦ by positivity) hg)

-- todo: generalize the type of `f`
lemma _root_.AnalyticAt.hasFPowerSeriesAt {f : ℝ → ℝ} {x : ℝ} (h : AnalyticAt ℝ f x) :
    HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℝ (fun n ↦ iteratedDeriv n f x / n.factorial)) x := by
  obtain ⟨p, hp⟩ := h
  convert hp
  obtain ⟨r, hpr⟩ := hp
  ext n u
  have h_fact_smul := hpr.factorial_smul 1
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, prod_const, card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul, one_pow, one_mul] at h_fact_smul
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_eq_mul_left_iff]
  left
  rw [div_eq_iff, mul_comm, h_fact_smul, ← iteratedDeriv_eq_iteratedFDeriv]
  norm_cast
  exact Nat.factorial_ne_zero _

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measure Ω} {t u v : ℝ}

lemma analyticAt_re_ofReal {f : ℂ → ℂ} {x : ℝ} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℝ (fun x : ℝ ↦ (f x).re) x :=
  (Complex.reCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

section MomentGeneratingFunction

section Deriv

lemma hasDerivAt_mgf (h : t ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (mgf X μ) (μ[fun ω ↦ X ω * exp (t * X ω)]) t := by
  convert hasDerivAt_integral_pow_mul_exp_real h 0
  · simp [mgf]
  · simp

lemma hasDerivAt_iteratedDeriv_mgf (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (iteratedDeriv n (mgf X μ)) μ[fun ω ↦ X ω ^ (n + 1) * exp (t * X ω)] t := by
  induction n generalizing t with
  | zero => simp [hasDerivAt_mgf ht]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (mgf X μ))
        =ᶠ[𝓝 t] fun t ↦ μ[fun ω ↦ X ω ^ (n + 1) * exp (t * X ω)] := by
      have h_mem : ∀ᶠ y in 𝓝 t, y ∈ interior (integrableExpSet X μ) :=
        isOpen_interior.eventually_mem ht
      filter_upwards [h_mem] with y hy using HasDerivAt.deriv (hn hy)
    rw [EventuallyEq.hasDerivAt_iff this]
    exact hasDerivAt_integral_pow_mul_exp_real ht (n + 1)

lemma iteratedDeriv_mgf (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    iteratedDeriv n (mgf X μ) t = μ[fun ω ↦ X ω ^ n * exp (t * X ω)] := by
  induction n generalizing t with
  | zero => simp [mgf]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_mgf ht n).deriv

/-- The derivatives of the moment generating function at zero are the moments. -/
lemma iteratedDeriv_mgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    iteratedDeriv n (mgf X μ) 0 = μ[X ^ n] := by
  simp [iteratedDeriv_mgf h n]

lemma deriv_mgf (h : v ∈ interior (integrableExpSet X μ)) :
    deriv (mgf X μ) v = μ[fun ω ↦ X ω * exp (v * X ω)] :=
  (hasDerivAt_mgf h).deriv

lemma deriv_mgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) :
    deriv (mgf X μ) 0 = μ[X] := by
  simp [deriv_mgf h]

end Deriv

lemma analyticAt_mgf (ht : t ∈ interior (integrableExpSet X μ)) :
    AnalyticAt ℝ (mgf X μ) t := by
  rw [← re_complexMGF_ofReal']
  refine analyticAt_re_ofReal ?_
  exact analyticAt_complexMGF (by simp [ht])

/-- The moment generating function is analytic on the interior of the interval on which it is
defined. -/
lemma analyticOnNhd_mgf : AnalyticOnNhd ℝ (mgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx ↦ analyticAt_mgf hx

lemma hasFPowerSeriesAt_mgf (hv : v ∈ interior (integrableExpSet X μ)) :
    HasFPowerSeriesAt (mgf X μ)
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n ↦ (μ[fun ω ↦ X ω ^ n * exp (v * X ω)] : ℝ) / n.factorial)) v := by
  convert (analyticAt_mgf hv).hasFPowerSeriesAt
  rw [iteratedDeriv_mgf hv]

section Analytic

-- todo: remove everything below this point (proving what needs to remain from what we have above)

lemma summable_integral_abs_mul_exp
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) :
    Summable fun (i : ℕ) ↦ μ[fun ω ↦ |X ω| ^ i / i.factorial * |t| ^ i * exp (v * X ω)] := by
  by_cases ht : t = 0
  · simp only [ht, abs_zero]
    refine summable_of_ne_finset_zero (s := {0}) (fun n hn ↦ ?_)
    rw [zero_pow]
    · simp
    · simpa using hn
  suffices Summable fun i ↦ ∫ ω, (|t| * |X ω|) ^ i / i.factorial * exp (v * X ω) ∂μ by
    simp_rw [mul_pow] at this
    convert this using 4 with i ω
    ring
  have h_int (u : ℝ) (i : ℕ) :
      Integrable (fun ω ↦ (u * |X ω|) ^ i / i.factorial * exp (v * X ω)) μ := by
    simp_rw [mul_pow]
    simp_rw [mul_comm _ (exp (v * _)), mul_div]
    refine Integrable.div_const ?_ _
    simp_rw [mul_comm (exp _), mul_assoc]
    refine Integrable.const_mul ?_ _
    exact integrable_pow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg i
  refine summable_of_sum_range_le (c := μ[fun ω ↦ exp (|t| * |X ω| + v * X ω)])
    (fun _ ↦ integral_nonneg fun ω ↦ by positivity) fun n ↦ ?_
  rw [← integral_finset_sum]
  · refine integral_mono ?_ ?_ ?_
    · exact integrable_finset_sum (range n) fun i a ↦ h_int |t| i
    · exact integrable_exp_abs_mul_abs_add ht_int_pos ht_int_neg
    · intro ω
      simp only
      rw [← sum_mul, exp_add]
      gcongr
      exact sum_le_exp_of_nonneg (by positivity) _
  · exact fun i _ ↦ h_int _ i

lemma summable_integral_pow_abs_mul_exp_mul_abs
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) :
    Summable fun (i : ℕ) ↦ μ[fun ω ↦ |X ω| ^ i * exp (v * X ω)] / i.factorial * |t| ^ i := by
  simp_rw [← integral_div, ← integral_mul_right]
  have h_eq i ω : |X ω| ^ i * exp (v * X ω) / i.factorial * |t| ^ i
      = |X ω| ^ i / i.factorial * |t| ^ i * exp (v * X ω) := by ring
  simp_rw [h_eq]
  exact summable_integral_abs_mul_exp ht_int_pos ht_int_neg

lemma summable_integral_pow_mul_exp_mul
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) :
    Summable fun (i : ℕ) ↦ μ[fun ω ↦ X ω ^ i * exp (v * X ω)] / i.factorial * t ^ i := by
  refine (summable_integral_pow_abs_mul_exp_mul_abs ht_int_pos ht_int_neg).mono fun i ↦ ?_
  simp only [Pi.pow_apply, norm_mul, norm_div, norm_eq_abs, norm_natCast, norm_pow, abs_abs,
    Nat.abs_cast]
  refine mul_le_mul ?_ le_rfl (by positivity) (by positivity)
  rw [div_le_div_iff_of_pos_right (by positivity)]
  conv_rhs => rw [abs_of_nonneg (integral_nonneg (fun _ ↦ by positivity))]
  simp_rw [← norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp

lemma summable_integral_pow_mul (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (- t * X ω)) μ) :
    Summable fun (i : ℕ) ↦ μ[X ^ i] / i.factorial * t ^ i := by
  have h := summable_integral_pow_mul_exp_mul (μ := μ) (X := X) (v := 0) (t := t) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

lemma mgf_add_eq_tsum (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) :
    mgf X μ (v + t) = ∑' n, μ[fun ω ↦ X ω ^ n * exp (v * X ω)] / n.factorial * t ^ n := by
  by_cases ht : t = 0
  · rw [tsum_eq_single 0]
    · simp [ht, mgf]
    · intro n hn
      simp [zero_pow hn, ht]
  have h_int_pow i : Integrable (fun ω ↦ X ω ^ i / i.factorial * t ^ i * exp (v * X ω)) μ := by
    simp_rw [mul_comm _ (exp _), ← mul_assoc, ← mul_div_assoc, mul_comm (exp _)]
    refine (Integrable.div_const ?_ _).mul_const _
    exact integrable_pow_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg i
  suffices Tendsto (fun n ↦ |mgf X μ (v + t)
        - μ[fun ω ↦ ∑ i in range n, X ω ^ i / i.factorial * t ^ i * exp (v * X ω)]|)
      atTop (𝓝 0) by
    change Tendsto (abs ∘ _) _ _ at this
    rw [← tendsto_zero_iff_abs_tendsto_zero] at this
    have h_eq n : μ[fun ω ↦ ∑ i ∈ range n, X ω ^ i / i.factorial * t ^ i * exp (v * X ω)]
        = ∑ i ∈ range n, μ[fun ω ↦ X ω ^ i * exp (v * X ω)] / i.factorial * t ^ i := by
      rw [integral_finset_sum]
      · congr with n
        rw [← integral_div, ← integral_mul_right]
        congr with ω
        ring
      · exact fun i _ ↦ h_int_pow i
    simp_rw [h_eq] at this
    suffices Tendsto (fun n ↦
          ∑ i ∈ range n, μ[fun ω ↦ X ω ^ i * exp (v * X ω)] / i.factorial * t ^ i)
        atTop (𝓝 (mgf X μ (v + t))) by
      refine tendsto_nhds_unique this ?_
      refine HasSum.Multipliable.tendsto_sum_tsum_nat ?_
      exact summable_integral_pow_mul_exp_mul ht_int_pos ht_int_neg
    rwa [← tendsto_const_sub_iff (b := mgf X μ (v + t)), sub_self]
  have h_le n : |mgf X μ (v + t)
        - μ[fun ω ↦ ∑ i ∈ range n, X ω ^ i / ↑i.factorial * t ^ i * exp (v * X ω)]|
      ≤ ∑' i : {j // j ∉ range n},
        μ[fun ω ↦ |X ω| ^ (i : ℕ) * exp (v * X ω)] / (i : ℕ).factorial * |t| ^ (i : ℕ) := by
    calc |mgf X μ (v + t)
        - μ[fun ω ↦ ∑ i ∈ range n, X ω ^ i / ↑i.factorial * t ^ i * exp (v * X ω)]|
    _ = |μ[fun ω ↦ ∑' i : {j // j ∉ range n},
        X ω ^ (i : ℕ) / (i : ℕ).factorial * t ^ (i : ℕ) * exp (v * X ω)]| := by
      simp_rw [mgf]
      rw [← integral_sub ht_int_pos (integrable_finset_sum _ (fun i _ ↦ h_int_pow i))]
      congr with ω
      rw [add_mul, add_comm, exp_add, exp_eq_tsum, sub_eq_iff_eq_add']
      have : ∑' n, (t * X ω) ^ n / n.factorial = ∑' n, X ω ^ n / n.factorial * t ^ n := by
        simp_rw [mul_pow]
        congr with n
        ring
      rw [this, ← tsum_mul_right]
      refine (sum_add_tsum_compl ?_).symm
      suffices Summable fun i ↦ (t * X ω) ^ i / i.factorial * exp (v * X ω) by
        convert this using 2 with i
        ring
      exact Summable.mul_right _ <| summable_pow_div_factorial _
    _ = |∑' i : {j // j ∉ range n},
        μ[fun ω ↦ X ω ^ (i : ℕ) * exp (v * X ω)] / (i : ℕ).factorial * t ^ (i : ℕ)| := by
      have h_eq i ω : X ω ^ i / ↑i.factorial * t ^ i * exp (v * X ω)
          = X ω ^ i * exp (v * X ω) / ↑i.factorial * t ^ i := by ring
      simp_rw [h_eq]
      rw [← integral_tsum_of_summable_integral_norm]
      · simp_rw [← integral_div, ← integral_mul_right]
      · refine fun i ↦ (Integrable.div_const ?_ _).mul_const _
        exact integrable_pow_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg _
      · simp only [norm_mul, norm_div, norm_pow, norm_eq_abs, norm_natCast, Nat.abs_cast]
        simp_rw [integral_mul_right, integral_div, abs_exp]
        exact (summable_integral_pow_abs_mul_exp_mul_abs ht_int_pos ht_int_neg).subtype (range n)ᶜ
    _ ≤ ∑' i : {j // j ∉ range n},
        |μ[fun ω ↦ X ω ^ (i : ℕ) * exp (v * X ω)] / (i : ℕ).factorial * t ^ (i : ℕ)| := by
      simp_rw [← norm_eq_abs]
      refine norm_tsum_le_tsum_norm ?_
      rw [summable_norm_iff]
      exact (summable_integral_pow_mul_exp_mul ht_int_pos ht_int_neg).subtype (range n)ᶜ
    _ ≤ ∑' i : {j // j ∉ range n},
          μ[fun ω ↦ |X ω| ^ (i : ℕ) * exp (v * X ω)] / (i : ℕ).factorial * |t| ^ (i : ℕ) := by
      simp only [Pi.pow_apply]
      refine tsum_mono ?_ ?_ fun n ↦ ?_
      · rw [summable_abs_iff]
        exact (summable_integral_pow_mul_exp_mul ht_int_pos ht_int_neg).subtype (range n)ᶜ
      · exact (summable_integral_pow_abs_mul_exp_mul_abs ht_int_pos ht_int_neg).subtype (range n)ᶜ
      · rw [abs_mul, abs_div, Nat.abs_cast, abs_pow]
        gcongr
        simp_rw [← norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans ?_
        simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) ?_ ?_ h_le
  · refine (tendsto_tsum_compl_atTop_zero
      (fun i ↦ μ[fun ω ↦ |X ω| ^ (i : ℕ) * exp (v * X ω)]
        / (i : ℕ).factorial * |t| ^ (i : ℕ))).comp ?_
    exact tendsto_finset_range
  · intro n
    positivity

lemma mgf_eq_tsum (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (- t * X ω)) μ) :
    mgf X μ t = ∑' n, μ[X ^ n] / n.factorial * t ^ n := by
  have h := mgf_add_eq_tsum (μ := μ) (X := X) (v := 0) (t := t) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

end Analytic

end MomentGeneratingFunction

end ProbabilityTheory
