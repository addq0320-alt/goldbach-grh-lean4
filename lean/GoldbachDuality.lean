import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Identities and inequalities used in GoldbachDuality.pdf.
Tested with Lean 4.19.0 and mathlib v4.19.0.
Run in a matching mathlib project:
  lake env lean --trust=0 -DwarningAsError=true GoldbachDuality.lean

The continuous Fourier identity, Selberg and Fejér estimates, and six-coordinate
inclusion-exclusion argument are proved in the accompanying PDF.
-/

noncomputable section

namespace GoldbachDuality
open Finset MeasureTheory
open scoped BigOperators RealInnerProductSpace

/-- Green function on (0,l), its diagonal, and the logarithm of the odds. -/
def green (l x y : ℝ) : ℝ := min x y * (l - max x y) / l
def diag (l x : ℝ) : ℝ := x * (l - x) / l
def coord (l x : ℝ) : ℝ := Real.log (x / (l - x))

private theorem green_sq_ordered {l x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < l) :
    green l x y ^ 2 = diag l x * diag l y * Real.exp (-|coord l x - coord l y|) := by
  have hxl : 0 < l - x := by linarith
  have hyl : 0 < l - y := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hl : 0 < l := by linarith
  have hratio : x / (l-x) ≤ y / (l-y) := by
    apply (div_le_div_iff₀ hxl hyl).2
    nlinarith only [mul_nonneg hl.le (sub_nonneg.mpr hxy)]
  have hlog : coord l x ≤ coord l y := Real.log_le_log (div_pos hx hxl) hratio
  rw [abs_of_nonpos (sub_nonpos.mpr hlog), neg_neg, Real.exp_sub]
  simp only [coord, Real.exp_log (div_pos hx hxl), Real.exp_log (div_pos hy0 hyl),
    green, diag, min_eq_left hxy, max_eq_right hxy]
  field_simp
  ring

/-- The squared Dirichlet Green kernel becomes the exponential covariance kernel. -/
theorem green_sq_factorization {l x y : ℝ} (hx : 0 < x) (hxl : x < l)
    (hy : 0 < y) (hyl : y < l) :
    green l x y ^ 2 = diag l x * diag l y * Real.exp (-|coord l x - coord l y|) := by
  rcases le_total x y with h | h
  · exact green_sq_ordered hx h hyl
  · have he := green_sq_ordered hy h hxl
    simpa only [green, min_comm y x, max_comm y x, mul_comm (diag l y) (diag l x),
      abs_sub_comm (coord l y) (coord l x)] using he

private theorem green_min_ordered {l x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < l) :
    green l x y ^ 2 =
      (x*y/l)^2 * min (((l-x)/x)^2) (((l-y)/y)^2) := by
  have hy0 := lt_of_lt_of_le hx hxy
  have hl : 0 < l := by linarith
  have hr : (l-y)/y ≤ (l-x)/x := by
    apply (div_le_div_iff₀ hy0 hx).2
    nlinarith only [mul_nonneg hl.le (sub_nonneg.mpr hxy)]
  have hs := pow_le_pow_left₀ (div_nonneg (sub_nonneg.mpr hy.le) hy0.le) hr 2
  rw [min_eq_right hs, green, min_eq_left hxy, max_eq_right hxy]
  field_simp
  ring

/-- The positive threshold-mixture factorization for the physical cutoff. -/
theorem green_min_factorization {l x y : ℝ} (hx : 0 < x) (hxl : x < l)
    (hy : 0 < y) (hyl : y < l) :
    green l x y ^ 2 =
      (x*y/l)^2 * min (((l-x)/x)^2) (((l-y)/y)^2) := by
  rcases le_total x y with h | h
  · exact green_min_ordered hx h hyl
  · have he := green_min_ordered hy h hxl
    simpa only [green, min_comm y x, max_comm y x, mul_comm y x,
      min_comm (((l-y)/y)^2) (((l-x)/x)^2)] using he

/-- Indicator of a positive threshold interval, with Lebesgue endpoints fixed. -/
def threshold (t : ℝ) : ℝ → ℝ := (Set.Ioc 0 t).indicator (fun _ => 1)

private theorem threshold_mul (x y r : ℝ) :
    threshold x r * threshold y r = threshold (min x y) r := by
  by_cases hx : r ∈ Set.Ioc 0 x <;> by_cases hy : r ∈ Set.Ioc 0 y
  · have h : r ∈ Set.Ioc 0 (min x y) := ⟨hx.1, le_min hx.2 hy.2⟩
    simp [threshold, hx, hy, h]
  · have h : r ∉ Set.Ioc 0 (min x y) := fun q => hy ⟨q.1, q.2.trans (min_le_right ..)⟩
    simp [threshold, hx, hy, h]
  · have h : r ∉ Set.Ioc 0 (min x y) := fun q => hx ⟨q.1, q.2.trans (min_le_left ..)⟩
    simp [threshold, hx, hy, h]
  · have h : r ∉ Set.Ioc 0 (min x y) := fun q => hx ⟨q.1, q.2.trans (min_le_left ..)⟩
    simp [threshold, hx, hy, h]

private theorem threshold_int (t : ℝ) (ht : 0 ≤ t) : (∫ r, threshold t r) = t := by
  rw [threshold, integral_indicator_const 1 measurableSet_Ioc, Real.volume_real_Ioc]
  simp [ht]

private theorem threshold_integrable (t : ℝ) : Integrable (threshold t) volume :=
  (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const.2 (Or.inr measure_Ioc_lt_top))

/-- For arbitrary signed atomic weights, the minimum-kernel double sum is
exactly a Lebesgue integral of a squared prefix sum. -/
theorem finite_prefix_energy {ι : Type*} (s : Finset ι) (w h : ι → ℝ)
    (hh : ∀ i ∈ s, 0 ≤ h i) :
    (∫ r, (∑ i ∈ s, w i * threshold (h i) r)^2) =
      ∑ i ∈ s, ∑ j ∈ s, w i*w j * min (h i) (h j) := by
  have expand (r : ℝ) : (∑ i ∈ s, w i * threshold (h i) r)^2 =
      ∑ i ∈ s, ∑ j ∈ s, (w i*w j)*threshold (min (h i) (h j)) r := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← threshold_mul]
    ring
  have hi (i j : ι) : Integrable (fun r => (w i*w j)*threshold (min (h i) (h j)) r) volume :=
    (threshold_integrable _).const_mul _
  simp_rw [expand]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hsi
    rw [integral_finset_sum _ (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro j hsj
    rw [integral_const_mul, threshold_int _ (le_min (hh i hsi) (hh j hsj))]
  · intro i _
    exact integrable_finset_sum _ (fun j _ => hi i j)

/-- The physical cutoff density is a probability density on the unit interval. -/
theorem beta_cutoff_mass : (∫ x in (0:ℝ)..1, 20*x^3*(1-x)) = 1 := by
  have e (x : ℝ) : 20*x^3*(1-x) = 20*(x^3-x^4) := by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub, integral_pow, integral_pow]
  · norm_num
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- A model majorant for the left endpoint loss, integrated exactly before
applying ε ≤ h. This gives the fourth power of the retained endpoint width. -/
theorem left_endpoint_majorant {h ε : ℝ} (hε : 0 ≤ ε) (heh : ε ≤ h) :
    (∫ x in (0:ℝ)..h, 20*x^3*(1+ε/x)^2) ≤ 30*h^4 := by
  have hh := hε.trans heh
  have expand (x : ℝ) : 20*x^3*(1+ε/x)^2 =
      20*x^3 + (40*ε)*x^2 + (20*ε^2)*x := by
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
      ring
  have val : (∫ x in (0:ℝ)..h, 20*x^3*(1+ε/x)^2) =
      5*h^4 + (40/3)*ε*h^3 + 10*ε^2*h^2 := by
    simp_rw [expand]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_id]
    · norm_num
      ring
    all_goals apply Continuous.intervalIntegrable; fun_prop
  rw [val]
  have h1 := mul_le_mul_of_nonneg_right heh (pow_nonneg hh 3)
  have h2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hε heh 2) (pow_nonneg hh 2)
  nlinarith only [h1, h2, pow_nonneg hh 4]

/-- The Beta(4,2) mass of a terminal interval vanishes quadratically. -/
theorem right_endpoint_mass {j : ℝ} (hj : 0 ≤ j) (hj1 : j ≤ 1) :
    (∫ x in (1-j)..1, 20*x^3*(1-x)) ≤ 10*j^2 := by
  have e (x : ℝ) : 20*x^3*(1-x) = 20*(x^3-x^4) := by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub, integral_pow, integral_pow]
  · norm_num
    have hp := mul_le_mul_of_nonneg_right hj1 (pow_nonneg hj 3)
    nlinarith only [hp, pow_nonneg hj 5, pow_nonneg hj 3]
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- The center test has the square of the tent function as its interval weight. -/
theorem center_test {l x : ℝ} (hx : 0 < x) (hxl : x < l) :
    diag l x * Real.exp (-|coord l x|) = (min x (l-x))^2 / l := by
  have hl : 0 < l := by linarith
  have he := green_sq_factorization hx hxl (show 0 < l/2 by linarith) (show l/2 < l by linarith)
  have hd : diag l (l/2) = l/4 := by unfold diag; field_simp; ring
  have hc : coord l (l/2) = 0 := by
    have hr : l / 2 / (l - l / 2) = 1 := (div_eq_one_iff_eq (by linarith)).2 (by ring)
    simp [coord, hr]
  rw [hd, hc, sub_zero] at he
  by_cases ho : x ≤ l/2
  · simp only [green, min_eq_left ho, max_eq_right ho] at he
    rw [min_eq_left (by linarith : x ≤ l-x)]
    field_simp at he ⊢
    nlinarith only [he, sq_pos_of_pos hl]
  · have ho' : l/2 ≤ x := le_of_lt (lt_of_not_ge ho)
    simp only [green, min_eq_right ho', max_eq_left ho'] at he
    rw [min_eq_right (by linarith : l-x ≤ x)]
    field_simp at he ⊢
    nlinarith only [he, sq_pos_of_pos hl]

/-- Exact location and weight of each arithmetic atom in the new coordinates. -/
theorem arithmetic_coordinates {n m : ℝ} (hn : 0 < n) (hb : m < 2*n/3) :
    diag (1/3) (m/n - 1/3) = (3*m-n)*(2*n-3*m)/(3*n^2) ∧
    coord (1/3) (m/n - 1/3) = Real.log ((3*m-n)/(2*n-3*m)) := by
  constructor
  · unfold diag
    field_simp
    ring
  · unfold coord
    congr 1
    have hpos : 0 < 2*n-3*m := by linarith
    have hden : (1/3 : ℝ) - (m/n-1/3) = (2*n-3*m)/(3*n) := by field_simp; ring
    rw [hden]
    field_simp
    ring

/-- Lebesgue integral of both symmetric halves of the explicit center test. -/
theorem center_integral {l : ℝ} (hl : 0 < l) :
    2 * (∫ x in (0:ℝ)..(l/2), x^2/l) = l^2/12 := by
  rw [intervalIntegral.integral_div, integral_pow]
  norm_num
  field_simp
  ring

/-- Integrating the squared Green kernel against Lebesgue measure gives a
polynomial potential, the optimal test for the missing-pair model. -/
theorem uniform_model_potential {l x : ℝ} (hl : 0 < l) :
    ((l-x)/l)^2 * (∫ v in (0:ℝ)..x, v^2) +
      (x/l)^2 * (∫ v in (0:ℝ)..(l-x), v^2) = (l/3)*(diag l x)^2 := by
  simp only [integral_pow]
  unfold diag
  norm_num
  field_simp
  ring

/-- The squared Hilbert-Schmidt energy of Lebesgue measure on the interval. -/
theorem uniform_model_energy {l : ℝ} (hl : 0 < l) :
    (∫ x in (0:ℝ)..l, (l/3)*(diag l x)^2) = l^4/90 := by
  have he (x : ℝ) : (l/3)*(diag l x)^2 =
      (l^2*x^2 - (2*l)*x^3 + x^4)/(3*l) := by unfold diag; field_simp; ring
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add,
    intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
  · norm_num
    field_simp
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

section Hilbert
variable {ι α H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The centered feature sum can have signed coefficients. -/
theorem finite_feature_energy (s : Finset α) (w : α → ℝ) (φ : α → H) :
    ‖∑ i ∈ s, w i • φ i‖^2 =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * ⟪φ i, φ j⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- Polynomial Young inequality for the dual exponents 6 and 6/5. -/
theorem young_six {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    6*x*y^5 ≤ x^6 + 5*y^6 := by
  have hp : 0 ≤ x^4 + 2*x^3*y + 3*x^2*y^2 + 4*x*y^3 + 5*y^4 := by positivity
  nlinarith only [mul_nonneg (sq_nonneg (x-y)) hp]

/-- Sixth-power dual objective, with dual variable parametrized by ||q||^4 q. -/
def dualObjective (s : Finset ι) (z q : ι → H) : ℝ :=
  ∑ i ∈ s, (6 * ‖q i‖^4 * ⟪z i, q i⟫ - 5 * ‖q i‖^6)

/-- The full supremum and its maximizing witness q=z, including z=0. -/
theorem hilbert_sixth_dual (s : Finset ι) (z : ι → H) :
    IsGreatest (Set.range (dualObjective s z)) (∑ i ∈ s, ‖z i‖^6) := by
  constructor
  · refine ⟨z, ?_⟩
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_self_eq_norm_sq]
    ring
  · rintro _ ⟨q, rfl⟩
    apply Finset.sum_le_sum
    intro i _
    have hc : 6*‖q i‖^4*⟪z i, q i⟫ ≤ 6*‖q i‖^4*(‖z i‖*‖q i‖) :=
      mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (by positivity)
    nlinarith only [hc, young_six (norm_nonneg (z i)) (norm_nonneg (q i))]

/-- The unit-ball version of the sharp 6/5 dual, with an explicit maximizer. -/
theorem normalized_sixth_dual (s : Finset ι) (z : ι → H)
    (hz : ∑ i ∈ s, ‖z i‖^6 = 1) :
    IsGreatest {v : ℝ | ∃ q : ι → H, (∑ i ∈ s, ‖q i‖^6) ≤ 1 ∧
      (∑ i ∈ s, ‖q i‖^4 * ⟪z i, q i⟫) = v} 1 := by
  constructor
  · refine ⟨z, hz.le, ?_⟩
    calc
      _ = ∑ i ∈ s, ‖z i‖^6 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_self_eq_norm_sq]
        ring
      _ = 1 := hz
  · rintro _ ⟨q, hq, rfl⟩
    have h := (hilbert_sixth_dual s z).2 (Set.mem_range_self q)
    unfold dualObjective at h
    simp_rw [mul_assoc (6:ℝ)] at h
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hz] at h
    linarith only [h, hq]

/-- A vector with norm equal to the operator norm yields a pair of unit-ball
test vectors attaining the operator norm in a real Hilbert space. -/
theorem norming_pair (T : H →L[ℝ] H)
    (attained : ∃ u : H, ‖u‖ ≤ 1 ∧ ‖T u‖ = ‖T‖) :
    ∃ u v : H, ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧ ⟪T u, v⟫ = ‖T‖ := by
  obtain ⟨u, hu, he⟩ := attained
  by_cases hz : ‖T u‖ = 0
  · refine ⟨u, 0, hu, by simp, ?_⟩
    rw [inner_zero_right, ← he, hz]
  · refine ⟨u, (‖T u‖)⁻¹ • T u, hu, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hz]
    · rw [real_inner_smul_right, real_inner_self_eq_norm_sq, ← he]
      field_simp
      ring

/-- Rank-one dual tests for a finite family of norm-attaining Hilbert-space
operators. The normalization of the left family fixes the maximum at one.
In the complex case the scalar objective is the real part of the pairing. -/
theorem operator_sixth_dual (s : Finset ι) (T : ι → H →L[ℝ] H)
    (normed : (∑ i ∈ s, ‖T i‖^6) = 1)
    (attained : ∀ i, ∃ u : H, ‖u‖ ≤ 1 ∧ ‖T i u‖ = ‖T i‖) :
    IsGreatest {r : ℝ | ∃ (b : ι → ℝ) (u v : ι → H),
      (∀ i ∈ s, 0 ≤ b i ∧ ‖u i‖ ≤ 1 ∧ ‖v i‖ ≤ 1) ∧
      (∑ i ∈ s, (b i)^6) ≤ 1 ∧
      (∑ i ∈ s, (b i)^5 * ⟪T i (u i), v i⟫) = r} 1 := by
  classical
  constructor
  · choose u v hu hv he using fun i => norming_pair (T i) (attained i)
    refine ⟨fun i => ‖T i‖, u, v,
      fun i _ => ⟨norm_nonneg _, hu i, hv i⟩, normed.le, ?_⟩
    simp_rw [he, ← pow_succ]
    exact normed
  · rintro _ ⟨b, u, v, hb, hs, rfl⟩
    have hpoint (i : ι) (hi : i ∈ s) :
        6 * ((b i)^5 * ⟪T i (u i), v i⟫) ≤ ‖T i‖^6 + 5*(b i)^6 := by
      obtain ⟨hbi, hui, hvi⟩ := hb i hi
      have hu : ‖T i (u i)‖ ≤ ‖T i‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          ((mul_le_mul_of_nonneg_left hui (norm_nonneg _)).trans_eq (mul_one _))
      have hip : ⟪T i (u i), v i⟫ ≤ ‖T i‖ := by
        calc
          _ ≤ ‖T i (u i)‖ * ‖v i‖ := real_inner_le_norm _ _
          _ ≤ ‖T i (u i)‖ * 1 := mul_le_mul_of_nonneg_left hvi (norm_nonneg _)
          _ ≤ _ := by simpa using hu
      have hm := mul_le_mul_of_nonneg_left hip
        (show 0 ≤ 6*(b i)^5 by positivity)
      nlinarith only [hm, young_six (norm_nonneg (T i)) hbi]
    have hh := Finset.sum_le_sum hpoint
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, normed] at hh
    linarith only [hh, hs]

end Hilbert

/-- One forest edge can be integrated away at the cost of the interval mass cap. -/
theorem forest_leaf {α β : Type*} (s : Finset α) (t : Finset β)
    (parent : α → ℝ) (child : α → β → ℝ) {cap : ℝ}
    (hp : ∀ i ∈ s, 0 ≤ parent i) (hc : ∀ i ∈ s, ∑ j ∈ t, child i j ≤ cap) :
    (∑ i ∈ s, ∑ j ∈ t, parent i * child i j) ≤ cap * ∑ i ∈ s, parent i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [← Finset.mul_sum, mul_comm cap]
  exact mul_le_mul_of_nonneg_left (hc i hi) (hp i hi)

/-- Successively integrating a finite list of transitions. A state records
previous vertices, so each transition may choose its parent from the history. -/
def forestMass {α κ : Type*} (s : Finset α) (next : κ → α → κ) :
    List ((κ → α → ℝ) × ℝ) → κ → ℝ
  | [], _ => 1
  | edge :: tail, state =>
      ∑ x ∈ s, edge.1 state x * forestMass s next tail (next state x)

private theorem product_of_nonneg (xs : List ℝ) (h : ∀ x ∈ xs, 0 ≤ x) :
    0 ≤ xs.prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact mul_nonneg (h x (List.mem_cons_self ..))
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- The tree/forest integration bound for arbitrarily many finite steps,
with separate mass caps for roots and for edges. -/
theorem forest_mass_bound {α κ : Type*} (s : Finset α) (next : κ → α → κ)
    (edges : List ((κ → α → ℝ) × ℝ))
    (caps : ∀ e ∈ edges, 0 ≤ e.2 ∧ (∀ h x, x ∈ s → 0 ≤ e.1 h x) ∧
      ∀ h, (∑ x ∈ s, e.1 h x) ≤ e.2) (h : κ) :
    forestMass s next edges h ≤ (edges.map Prod.snd).prod := by
  induction edges generalizing h with
  | nil => simp [forestMass]
  | cons e tail ih =>
    have he := caps e (List.mem_cons_self ..)
    have ht := fun f (hf : f ∈ tail) => caps f (List.mem_cons_of_mem _ hf)
    have hp : 0 ≤ (tail.map Prod.snd).prod :=
      product_of_nonneg _ (fun x hx => by
        obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hx
        exact (ht f hf).1)
    simp only [forestMass, List.map_cons, List.prod_cons]
    calc
      _ ≤ ∑ x ∈ s, e.1 h x * (tail.map Prod.snd).prod :=
        Finset.sum_le_sum fun x hx =>
          mul_le_mul_of_nonneg_left (ih ht (next h x)) (he.2.1 h x hx)
      _ = (∑ x ∈ s, e.1 h x) * (tail.map Prod.snd).prod := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (he.2.2 h) hp

/-- A graph with at most four isolated vertices always supplies at least
two small factors. The parameter A controls absorption of its contribution. -/
theorem absorb_mixed {t d A : ℝ} (ht : 0 ≤ t) (hd : 0 ≤ d) (hA : 1 ≤ A)
    (s p : ℕ) (hs : s + p = 6) (hp : 2 ≤ p) :
    t^s * d^p ≤ (1/A^2)*t^6 + A^s*d^6 := by
  have ha : 0 < A := by linarith
  by_cases h : t ≤ A*d
  · have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht h s) (pow_nonneg hd p)
    rw [mul_pow, mul_assoc, ← pow_add, hs] at hh
    linarith only [hh, mul_nonneg (by positivity : 0 ≤ 1/A^2) (pow_nonneg ht 6)]
  · have h' : A*d ≤ t := le_of_lt (lt_of_not_ge h)
    have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg ha.le hd) h' p)
      (pow_nonneg ht s)
    rw [mul_pow, ← pow_add, hs] at hb
    have hpow : A^2 ≤ A^p := pow_le_pow_right₀ hA hp
    have hh : A^2*(t^s*d^p) ≤ t^6 := by
      calc
        _ ≤ A^p*(t^s*d^p) := mul_le_mul_of_nonneg_right hpow (by positivity)
        _ = t^s*(A^p*d^p) := by ring
        _ ≤ _ := hb
    have hh' : t^s*d^p ≤ t^6/A^2 := (le_div_iff₀ (by positivity)).2 (by linarith only [hh])
    have hrest : 0 ≤ A^s*d^6 := by positivity
    rw [one_div, inv_mul_eq_div]
    linarith only [hh', hrest]

/-- Absorbing the near-collision terms leaves a signed separated term. -/
theorem far_remainder_bound {M R e : ℝ} (h : |M-R| ≤ M/2+e) :
    M ≤ 2*(|R|+e) := by
  linarith only [(abs_le.mp h).2, le_abs_self R]

end GoldbachDuality

open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked := #[``GoldbachDuality.green_sq_factorization, ``GoldbachDuality.green_min_factorization,
    ``GoldbachDuality.finite_prefix_energy, ``GoldbachDuality.beta_cutoff_mass,
    ``GoldbachDuality.left_endpoint_majorant, ``GoldbachDuality.right_endpoint_mass,
    ``GoldbachDuality.center_test,
    ``GoldbachDuality.arithmetic_coordinates, ``GoldbachDuality.center_integral,
    ``GoldbachDuality.uniform_model_potential, ``GoldbachDuality.uniform_model_energy,
    ``GoldbachDuality.finite_feature_energy,
    ``GoldbachDuality.young_six, ``GoldbachDuality.hilbert_sixth_dual,
    ``GoldbachDuality.normalized_sixth_dual, ``GoldbachDuality.norming_pair,
    ``GoldbachDuality.operator_sixth_dual, ``GoldbachDuality.forest_leaf,
    ``GoldbachDuality.forest_mass_bound, ``GoldbachDuality.absorb_mixed,
    ``GoldbachDuality.far_remainder_bound]
  for name in checked do
    let deps ← Lean.collectAxioms name
    unless deps.all allowed.contains do
      throwError "Unexpected axiom in {name}: {deps}"
    logInfo m!"{name}: {deps.qsort Name.lt |>.toList}"
