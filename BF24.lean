import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Positivity

/-!
# BF'24 Note: elementary inequalities

Inequalities used in our short note on Buchbinder–Feldman (FOCS 2024 /
SICOMP 2024). All classical; formalised here for verification.

## Main results

* `log_weak`        : `s/(1+s) ≤ log(1+s)` for `s ≥ 0` (from `Real.add_one_le_exp`).
* `log_pade`        : `2x/(2+x) ≤ log(1+x)` for `x ≥ 0` (Padé bound, via derivative).
* `log_tail4`       : `t - t²/2 + t³/3 - t⁴/4 ≤ log(1+t)` for `t ≥ 0`
                      (alternating-series tail; proof via `h'(t) = t⁴/(1+t) ≥ 0`).
* `bf24_lemma1`     : `(1+1/l)^l · (1+1/l)     ≥ e` for integer `l ≥ 1`.
* `bf24_lemma1pp`   : `(1+1/l)^l · (1+1/(2l))  ≥ e` for integer `l ≥ 1`  (Pólya–Szegő).
* `bf24_sharp`      : `(1+1/l)^l · exp(1/(2l) - 1/(3l²) + 1/(4l³)) ≥ e`
                      (asymptotically sharp: matches true expansion through `1/l³`).
-/

namespace BF24

open Real

/-! ### Weak log bound (via `add_one_le_exp`) -/

/-- For `s ≥ 0`, `s/(1+s) ≤ log(1+s)`. -/
lemma log_weak {s : ℝ} (hs : 0 ≤ s) : s / (1 + s) ≤ log (1 + s) := by
  have h1 : (0 : ℝ) < 1 + s := by linarith
  -- From `Real.add_one_le_exp` with argument `-log(1+s)`:
  --   1 + (-log(1+s)) ≤ exp(-log(1+s)) = (1+s)⁻¹
  have hbound : 1 - log (1 + s) ≤ (1 + s)⁻¹ := by
    have := Real.add_one_le_exp (-log (1 + s))
    rw [Real.exp_neg, Real.exp_log h1] at this
    linarith
  have h1ne : (1 + s) ≠ 0 := ne_of_gt h1
  have heq : s / (1 + s) = 1 - (1 + s)⁻¹ := by
    field_simp
    ring
  linarith

/-! ### Padé log bound (via derivative monotonicity)

We prove `2x/(2+x) ≤ log(1+x)` for `x ≥ 0`, where the derivative
of `h(x) = log(1+x) - 2x/(2+x)` is `x²/((1+x)(2+x)²) ≥ 0`.
-/

/-- Derivative of `log(1+t) - 2t/(2+t)` at `t > -1` is `t²/((1+t)(2+t)²)`. -/
lemma hasDerivAt_log_minus_pade {t : ℝ} (ht : -1 < t) :
    HasDerivAt (fun u => log (1 + u) - 2 * u / (2 + u))
      (t ^ 2 / ((1 + t) * (2 + t) ^ 2)) t := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : (0 : ℝ) < 2 + t := by linarith
  have h1ne : (1 : ℝ) + t ≠ 0 := ne_of_gt h1
  have h2ne : (2 : ℝ) + t ≠ 0 := ne_of_gt h2
  -- Derivative of log(1+t) is 1/(1+t).
  have d1 : HasDerivAt (fun u : ℝ => log (1 + u)) (1 / (1 + t)) t := by
    have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have hlog : HasDerivAt log (1 / (1 + t)) (1 + t) := by
      simpa using Real.hasDerivAt_log h1ne
    have := hlog.comp t hinner
    simpa using this
  -- Derivative of 2t/(2+t) is 4/(2+t)^2.
  have d2 : HasDerivAt (fun u : ℝ => 2 * u / (2 + u)) (4 / (2 + t) ^ 2) t := by
    have hnum : HasDerivAt (fun u : ℝ => 2 * u) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    have hden : HasDerivAt (fun u : ℝ => (2 : ℝ) + u) 1 t := by
      simpa using (hasDerivAt_id t).const_add (2 : ℝ)
    have hdiv := hnum.div hden h2ne
    convert hdiv using 1
    field_simp
    ring
  have hsub := d1.sub d2
  convert hsub using 1
  field_simp
  ring

/-- For `x ≥ 0`, `2x/(2+x) ≤ log(1+x)`. -/
lemma log_pade {x : ℝ} (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ log (1 + x) := by
  set h : ℝ → ℝ := fun t => log (1 + t) - 2 * t / (2 + t) with hdef
  have hzero : h 0 = 0 := by simp [hdef]
  suffices key : 0 ≤ h x by
    have : h x = log (1 + x) - 2 * x / (2 + x) := rfl
    linarith
  rw [← hzero]
  -- Show h is monotone on [0, ∞)
  have hmono : MonotoneOn h (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · -- ContinuousOn
      apply ContinuousOn.sub
      · apply ContinuousOn.log
        · exact (continuous_const.add continuous_id).continuousOn
        · intro t ht; simp at ht; linarith
      · apply ContinuousOn.div
        · exact (continuous_const.mul continuous_id).continuousOn
        · exact (continuous_const.add continuous_id).continuousOn
        · intro t ht; simp at ht; linarith
    · -- DifferentiableOn on interior = Ioi 0
      rw [interior_Ici]
      intro t ht
      simp at ht
      have := hasDerivAt_log_minus_pade (t := t) (by linarith)
      exact this.differentiableAt.differentiableWithinAt
    · -- deriv nonneg on interior
      intro t ht
      rw [interior_Ici] at ht
      simp at ht
      have hd := hasDerivAt_log_minus_pade (t := t) (by linarith)
      rw [hd.deriv]
      have h1 : (0 : ℝ) < 1 + t := by linarith
      have h2 : (0 : ℝ) < 2 + t := by linarith
      positivity
  exact hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr hx) hx

/-! ### Lemma 1 (weak): `(1+1/l)^l · (1+1/l) ≥ e` -/

lemma bf24_lemma1 (l : ℕ) (hl : 1 ≤ l) :
    Real.exp 1 ≤ (1 + 1 / (l : ℝ)) ^ l * (1 + 1 / (l : ℝ)) := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hlne : (l : ℝ) ≠ 0 := ne_of_gt hlR
  have hl1 : (0 : ℝ) < 1 + 1 / (l : ℝ) := by positivity
  -- log(1 + 1/l) ≥ (1/l)/(1 + 1/l) = 1/(l+1)
  have h_log : 1 / ((l : ℝ) + 1) ≤ Real.log (1 + 1 / (l : ℝ)) := by
    have hw := log_weak (s := 1 / (l : ℝ)) (by positivity)
    have heq : 1 / (l : ℝ) / (1 + 1 / (l : ℝ)) = 1 / ((l : ℝ) + 1) := by
      field_simp
    linarith
  -- Multiply by l+1 ≥ 1 > 0 to get 1 ≤ (l+1) · log(1 + 1/l)
  have hlp1 : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have h_mul : (1 : ℝ) ≤ ((l : ℝ) + 1) * Real.log (1 + 1 / (l : ℝ)) := by
    have := mul_le_mul_of_nonneg_left h_log (le_of_lt hlp1)
    have heq2 : ((l : ℝ) + 1) * (1 / ((l : ℝ) + 1)) = 1 := by
      field_simp
    linarith
  -- Exponentiate: exp 1 ≤ (1 + 1/l)^(l+1)
  have h_exp : Real.exp 1 ≤ (1 + 1 / (l : ℝ)) ^ (l + 1) := by
    have pow_pos : (0 : ℝ) < (1 + 1 / (l : ℝ)) ^ (l + 1) := pow_pos hl1 _
    rw [show Real.exp 1 = Real.exp ((1 : ℝ)) from rfl]
    calc Real.exp 1
        ≤ Real.exp (((l : ℝ) + 1) * Real.log (1 + 1 / (l : ℝ))) :=
          Real.exp_le_exp.mpr h_mul
      _ = (1 + 1 / (l : ℝ)) ^ (l + 1) := by
          rw [show ((l : ℝ) + 1) * Real.log (1 + 1 / (l : ℝ)) =
              Real.log ((1 + 1 / (l : ℝ)) ^ (l + 1)) from ?_,
            Real.exp_log pow_pos]
          rw [Real.log_pow]
          push_cast
          ring
  -- Rewrite (1+1/l)^(l+1) = (1+1/l)^l · (1+1/l)
  rwa [pow_succ] at h_exp

/-! ### Lemma 1'' (Pólya–Szegő): `(1+1/l)^l · (1+1/(2l)) ≥ e`

Uses `log_pade` twice with `x = 1/l` and `x = 1/(2l)` plus arithmetic.
-/

lemma bf24_lemma1pp (l : ℕ) (hl : 1 ≤ l) :
    Real.exp 1 ≤ (1 + 1 / (l : ℝ)) ^ l * (1 + 1 / (2 * (l : ℝ))) := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hlne : (l : ℝ) ≠ 0 := ne_of_gt hlR
  have hl1 : (0 : ℝ) < 1 + 1 / (l : ℝ) := by positivity
  have hl2 : (0 : ℝ) < 1 + 1 / (2 * (l : ℝ)) := by positivity
  have hl_ge_1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  -- Step 1: log(1 + 1/l) ≥ 2 / (2l + 1), using log_pade with x = 1/l.
  have hA : 2 / (2 * (l : ℝ) + 1) ≤ Real.log (1 + 1 / (l : ℝ)) := by
    have hp := log_pade (x := 1 / (l : ℝ)) (by positivity)
    have heq : 2 * (1 / (l : ℝ)) / (2 + 1 / (l : ℝ)) = 2 / (2 * (l : ℝ) + 1) := by
      field_simp
    linarith
  -- Step 2: log(1 + 1/(2l)) ≥ 2 / (4l + 1), using log_pade with x = 1/(2l).
  have hB : 2 / (4 * (l : ℝ) + 1) ≤ Real.log (1 + 1 / (2 * (l : ℝ))) := by
    have hp := log_pade (x := 1 / (2 * (l : ℝ))) (by positivity)
    have heq : 2 * (1 / (2 * (l : ℝ))) / (2 + 1 / (2 * (l : ℝ))) =
        2 / (4 * (l : ℝ) + 1) := by
      field_simp
      ring
    linarith
  -- Step 3: l · (2 / (2l+1)) + 2/(4l+1) ≥ 1.
  -- We have 2l/(2l+1) = 1 - 1/(2l+1), so we need 2/(4l+1) ≥ 1/(2l+1),
  -- i.e., 2(2l+1) ≥ 4l+1, i.e., 4l+2 ≥ 4l+1.
  have h_sum_bound : (1 : ℝ) ≤ (l : ℝ) * (2 / (2 * (l : ℝ) + 1)) +
      2 / (4 * (l : ℝ) + 1) := by
    have hd1 : (0 : ℝ) < 2 * (l : ℝ) + 1 := by linarith
    have hd2 : (0 : ℝ) < 4 * (l : ℝ) + 1 := by linarith
    rw [← sub_nonneg]
    have rewrite_eq : (l : ℝ) * (2 / (2 * (l : ℝ) + 1)) + 2 / (4 * (l : ℝ) + 1) - 1
        = 1 / ((2 * (l : ℝ) + 1) * (4 * (l : ℝ) + 1)) := by
      field_simp
      ring
    rw [rewrite_eq]
    positivity
  -- Step 4: l · log(1 + 1/l) + log(1 + 1/(2l)) ≥ 1.
  have h_log_sum : (1 : ℝ) ≤
      (l : ℝ) * Real.log (1 + 1 / (l : ℝ)) + Real.log (1 + 1 / (2 * (l : ℝ))) := by
    have hMul : (l : ℝ) * (2 / (2 * (l : ℝ) + 1)) ≤
        (l : ℝ) * Real.log (1 + 1 / (l : ℝ)) :=
      mul_le_mul_of_nonneg_left hA (le_of_lt hlR)
    linarith
  -- Step 5: exp(l · log(1+1/l) + log(1+1/(2l))) = (1+1/l)^l · (1+1/(2l))
  have h_exp : Real.exp 1 ≤ (1 + 1 / (l : ℝ)) ^ l * (1 + 1 / (2 * (l : ℝ))) := by
    calc Real.exp 1
        ≤ Real.exp ((l : ℝ) * Real.log (1 + 1 / (l : ℝ)) +
                    Real.log (1 + 1 / (2 * (l : ℝ)))) :=
          Real.exp_le_exp.mpr h_log_sum
      _ = Real.exp ((l : ℝ) * Real.log (1 + 1 / (l : ℝ))) *
              Real.exp (Real.log (1 + 1 / (2 * (l : ℝ)))) :=
          Real.exp_add _ _
      _ = (1 + 1 / (l : ℝ)) ^ l * (1 + 1 / (2 * (l : ℝ))) := by
          rw [Real.exp_log hl2]
          congr 1
          rw [show (l : ℝ) * Real.log (1 + 1 / (l : ℝ)) =
              Real.log ((1 + 1 / (l : ℝ)) ^ l) from ?_,
            Real.exp_log (pow_pos hl1 l)]
          rw [Real.log_pow]
  exact h_exp

/-! ### Alternating-series tail bound for `log`

We prove `log(1+t) ≥ t - t²/2 + t³/3 - t⁴/4` for `t ≥ 0`.  The derivative of
`h(t) := log(1+t) - (t - t²/2 + t³/3 - t⁴/4)` is `t⁴/(1+t) ≥ 0`, and `h(0)=0`.
-/

/-- Derivative of `log(1+t) - (t - t²/2 + t³/3 - t⁴/4)` at `t > -1` is `t⁴/(1+t)`. -/
lemma hasDerivAt_log_minus_tail4 {t : ℝ} (ht : -1 < t) :
    HasDerivAt (fun u => log (1 + u) - (u - u^2/2 + u^3/3 - u^4/4))
      (t^4 / (1 + t)) t := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h1ne : (1 : ℝ) + t ≠ 0 := ne_of_gt h1
  -- Derivative of log(1+u) at t is 1/(1+t)
  have d_log : HasDerivAt (fun u : ℝ => log (1 + u)) (1 / (1 + t)) t := by
    have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have hlog : HasDerivAt log (1 / (1 + t)) (1 + t) := by
      simpa using Real.hasDerivAt_log h1ne
    simpa using hlog.comp t hinner
  -- Derivatives of the monomials
  have e2 : HasDerivAt (fun u : ℝ => u^2) (2 * t) t := by
    simpa using (hasDerivAt_id t).pow 2
  have e3 : HasDerivAt (fun u : ℝ => u^3) (3 * t^2) t := by
    simpa using (hasDerivAt_id t).pow 3
  have e4 : HasDerivAt (fun u : ℝ => u^4) (4 * t^3) t := by
    simpa using (hasDerivAt_id t).pow 4
  have f2 : HasDerivAt (fun u : ℝ => u^2/2) t t := by
    have := e2.div_const (2 : ℝ)
    convert this using 1; ring
  have f3 : HasDerivAt (fun u : ℝ => u^3/3) (t^2) t := by
    have := e3.div_const (3 : ℝ)
    convert this using 1; ring
  have f4 : HasDerivAt (fun u : ℝ => u^4/4) (t^3) t := by
    have := e4.div_const (4 : ℝ)
    convert this using 1; ring
  have e1 : HasDerivAt (fun u : ℝ => u) (1 : ℝ) t := hasDerivAt_id t
  -- Derivative of the Taylor-4 polynomial
  have d_poly : HasDerivAt (fun u : ℝ => u - u^2/2 + u^3/3 - u^4/4)
                          (1 - t + t^2 - t^3) t :=
    ((e1.sub f2).add f3).sub f4
  have hsub := d_log.sub d_poly
  convert hsub using 1
  -- Show t^4/(1+t) = 1/(1+t) - (1 - t + t^2 - t^3)
  field_simp
  ring

/-- For `t ≥ 0`, `t - t²/2 + t³/3 - t⁴/4 ≤ log(1+t)`. -/
lemma log_tail4 {t : ℝ} (ht : 0 ≤ t) :
    t - t^2/2 + t^3/3 - t^4/4 ≤ log (1 + t) := by
  set h : ℝ → ℝ := fun u => log (1 + u) - (u - u^2/2 + u^3/3 - u^4/4) with hdef
  have hzero : h 0 = 0 := by simp [hdef]
  suffices key : 0 ≤ h t by
    have hval : h t = log (1 + t) - (t - t^2/2 + t^3/3 - t^4/4) := rfl
    linarith
  rw [← hzero]
  have hmono : MonotoneOn h (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · -- ContinuousOn
      apply ContinuousOn.sub
      · apply ContinuousOn.log
        · exact (continuous_const.add continuous_id).continuousOn
        · intro u hu; simp at hu; linarith
      · fun_prop
    · -- DifferentiableOn on interior = Ioi 0
      rw [interior_Ici]
      intro u hu
      simp at hu
      exact (hasDerivAt_log_minus_tail4 (t := u) (by linarith)).differentiableAt.differentiableWithinAt
    · -- deriv nonneg on interior
      intro u hu
      rw [interior_Ici] at hu
      simp at hu
      have hd := hasDerivAt_log_minus_tail4 (t := u) (by linarith)
      rw [hd.deriv]
      have h1 : (0 : ℝ) < 1 + u := by linarith
      have hu4 : 0 ≤ u^4 := by positivity
      positivity
  exact hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr ht) ht

/-! ### Sharp form: `(1+1/l)^l · exp(1/(2l) - 1/(3l²) + 1/(4l³)) ≥ e`

Using `log_tail4` with `t = 1/l`:  `log(1+1/l) ≥ 1/l - 1/(2l²) + 1/(3l³) - 1/(4l⁴)`.
Multiplying by `l` and rearranging gives the claim.  The bound is asymptotically
sharp: its exponentiated form matches `e⁻¹(1+1/(2l) - 5/(24l²) + 5/(48l³) + O(l⁻⁴))`
through order `1/l³`.
-/

lemma bf24_sharp (l : ℕ) (hl : 1 ≤ l) :
    Real.exp 1 ≤ (1 + 1 / (l : ℝ)) ^ l *
      Real.exp (1/(2*(l:ℝ)) - 1/(3*(l:ℝ)^2) + 1/(4*(l:ℝ)^3)) := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hlne : (l : ℝ) ≠ 0 := ne_of_gt hlR
  have hl1 : (0 : ℝ) < 1 + 1 / (l : ℝ) := by positivity
  -- Apply log_tail4 with t = 1/l (≥ 0)
  have hT : (1/(l:ℝ)) - (1/(l:ℝ))^2/2 + (1/(l:ℝ))^3/3 - (1/(l:ℝ))^4/4
            ≤ Real.log (1 + 1/(l:ℝ)) :=
    log_tail4 (by positivity)
  -- Multiply by l > 0
  have hMul : (l:ℝ) * ((1/(l:ℝ)) - (1/(l:ℝ))^2/2 + (1/(l:ℝ))^3/3 - (1/(l:ℝ))^4/4)
              ≤ (l:ℝ) * Real.log (1 + 1/(l:ℝ)) :=
    mul_le_mul_of_nonneg_left hT (le_of_lt hlR)
  -- Simplify the algebraic LHS
  have hSimp : (l:ℝ) * ((1/(l:ℝ)) - (1/(l:ℝ))^2/2 + (1/(l:ℝ))^3/3 - (1/(l:ℝ))^4/4)
              = 1 - 1/(2*(l:ℝ)) + 1/(3*(l:ℝ)^2) - 1/(4*(l:ℝ)^3) := by
    field_simp
  rw [hSimp] at hMul
  -- Rearrange: 1 ≤ l·log(1+1/l) + (1/(2l) - 1/(3l²) + 1/(4l³))
  have hSum : (1 : ℝ) ≤ (l:ℝ) * Real.log (1 + 1/(l:ℝ))
              + (1/(2*(l:ℝ)) - 1/(3*(l:ℝ)^2) + 1/(4*(l:ℝ)^3)) := by
    linarith
  -- Exponentiate
  have hExp_pow : Real.exp ((l:ℝ) * Real.log (1 + 1/(l:ℝ))) = (1 + 1/(l:ℝ))^l := by
    rw [show ((l:ℝ) * Real.log (1 + 1/(l:ℝ))) =
        Real.log ((1 + 1/(l:ℝ))^l) by rw [Real.log_pow]]
    exact Real.exp_log (pow_pos hl1 l)
  calc Real.exp 1
      ≤ Real.exp ((l:ℝ) * Real.log (1 + 1/(l:ℝ))
                + (1/(2*(l:ℝ)) - 1/(3*(l:ℝ)^2) + 1/(4*(l:ℝ)^3))) :=
        Real.exp_le_exp.mpr hSum
    _ = Real.exp ((l:ℝ) * Real.log (1 + 1/(l:ℝ))) *
          Real.exp (1/(2*(l:ℝ)) - 1/(3*(l:ℝ)^2) + 1/(4*(l:ℝ)^3)) :=
        Real.exp_add _ _
    _ = (1 + 1/(l:ℝ))^l *
          Real.exp (1/(2*(l:ℝ)) - 1/(3*(l:ℝ)^2) + 1/(4*(l:ℝ)^3)) := by
        rw [hExp_pow]

/-! ### Corollaries in the form used in the note -/

/-- Helper: from `1 ≤ A * B` with `A > 0`, deduce `A⁻¹ ≤ B`. -/
private lemma inv_le_of_one_le_mul {A B : ℝ} (hA : 0 < A) (h : 1 ≤ A * B) :
    A⁻¹ ≤ B := by
  have hA_ne : A ≠ 0 := ne_of_gt hA
  calc A⁻¹
      = A⁻¹ * 1 := (mul_one _).symm
    _ ≤ A⁻¹ * (A * B) := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hA))
    _ = B := by rw [← mul_assoc, inv_mul_cancel₀ hA_ne, one_mul]

/-- Lemma 1 in "reciprocal form": `(1+1/l)^{-l} ≤ (1/e)(1 + 1/l)`. -/
lemma bf24_lemma1_inv (l : ℕ) (hl : 1 ≤ l) :
    ((1 + 1 / (l : ℝ)) ^ l)⁻¹ ≤ (1 / Real.exp 1) * (1 + 1 / (l : ℝ)) := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hl1 : (0 : ℝ) < 1 + 1 / (l : ℝ) := by positivity
  have hpow : (0 : ℝ) < (1 + 1 / (l : ℝ)) ^ l := pow_pos hl1 l
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he_ne : Real.exp 1 ≠ 0 := ne_of_gt he
  have h := bf24_lemma1 l hl
  apply inv_le_of_one_le_mul hpow
  -- Goal: 1 ≤ (1+1/l)^l * ((1/exp 1) * (1+1/l))
  -- Multiply both sides by exp 1 > 0 to reduce to `h`.
  apply le_of_mul_le_mul_right _ he
  have rearrange : (1 + 1 / (l : ℝ)) ^ l * ((1 / Real.exp 1) * (1 + 1 / (l : ℝ)))
      * Real.exp 1 = (1 + 1 / (l : ℝ)) ^ l * (1 + 1 / (l : ℝ)) := by
    field_simp
  rw [one_mul, rearrange]
  exact h

/-- Lemma 1'' in "reciprocal form": `(1+1/l)^{-l} ≤ (1/e)(1 + 1/(2l))`. -/
lemma bf24_lemma1pp_inv (l : ℕ) (hl : 1 ≤ l) :
    ((1 + 1 / (l : ℝ)) ^ l)⁻¹ ≤ (1 / Real.exp 1) * (1 + 1 / (2 * (l : ℝ))) := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hl1 : (0 : ℝ) < 1 + 1 / (l : ℝ) := by positivity
  have hl2 : (0 : ℝ) < 1 + 1 / (2 * (l : ℝ)) := by positivity
  have hpow : (0 : ℝ) < (1 + 1 / (l : ℝ)) ^ l := pow_pos hl1 l
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he_ne : Real.exp 1 ≠ 0 := ne_of_gt he
  have h := bf24_lemma1pp l hl
  apply inv_le_of_one_le_mul hpow
  apply le_of_mul_le_mul_right _ he
  have rearrange : (1 + 1 / (l : ℝ)) ^ l * ((1 / Real.exp 1) * (1 + 1 / (2 * (l : ℝ))))
      * Real.exp 1 = (1 + 1 / (l : ℝ)) ^ l * (1 + 1 / (2 * (l : ℝ))) := by
    field_simp
  rw [one_mul, rearrange]
  exact h

/-- Sharp bound in reciprocal form:
    `(1+1/l)^{-l} ≤ (1/e)·exp(1/(2l) - 1/(3l²) + 1/(4l³))`. -/
lemma bf24_sharp_inv (l : ℕ) (hl : 1 ≤ l) :
    ((1 + 1 / (l : ℝ)) ^ l)⁻¹ ≤
    (1 / Real.exp 1) *
      Real.exp (1/(2*(l:ℝ)) - 1/(3*(l:ℝ)^2) + 1/(4*(l:ℝ)^3)) := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hl1 : (0 : ℝ) < 1 + 1 / (l : ℝ) := by positivity
  have hpow : (0 : ℝ) < (1 + 1 / (l : ℝ)) ^ l := pow_pos hl1 l
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he_ne : Real.exp 1 ≠ 0 := ne_of_gt he
  have h := bf24_sharp l hl
  apply inv_le_of_one_le_mul hpow
  apply le_of_mul_le_mul_right _ he
  have rearrange :
      (1 + 1 / (l : ℝ)) ^ l *
        ((1 / Real.exp 1) *
          Real.exp (1/(2*(l:ℝ)) - 1/(3*(l:ℝ)^2) + 1/(4*(l:ℝ)^3)))
      * Real.exp 1
      = (1 + 1 / (l : ℝ)) ^ l *
          Real.exp (1/(2*(l:ℝ)) - 1/(3*(l:ℝ)^2) + 1/(4*(l:ℝ)^3)) := by
    field_simp
  rw [one_mul, rearrange]
  exact h

end BF24
