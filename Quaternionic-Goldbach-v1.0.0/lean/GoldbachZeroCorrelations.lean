import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Finite parts of the zero-correlation reduction. Lean and mathlib 4.19.0. -/
noncomputable section
open Finset
open scoped BigOperators Classical

namespace GoldbachZeroCorrelations

/-- Unit-interval sampling step for the real observable |H|².
The derivative bound is used on the full interval before averaging. -/
theorem unit_interval_sample (F D : ℝ → ℝ) (hF : ∀ z, HasDerivAt F (D z) z)
    (hD : Continuous D) (a x : ℝ) (hx : x ∈ Set.Icc a (a+1)) :
    F x ≤ (∫ u in a..a+1, F u) + ∫ u in a..a+1, |D u| := by
  let V := ∫ u in a..a+1, |D u|
  have variation (u v : ℝ) (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ a+1) :
      |F v-F u| ≤ V := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hF z)
      (hD.intervalIntegrable u v)]
    exact (intervalIntegral.abs_integral_le_integral_abs huv).trans
      (intervalIntegral.integral_mono_interval hu huv hv
        (Filter.Eventually.of_forall (fun t => abs_nonneg (D t)))
        (hD.abs.intervalIntegrable a (a+1)))
  have point (y : ℝ) (hy : y ∈ Set.Icc a (a+1)) : F x ≤ F y + V := by
    rcases le_total y x with h | h
    · have v := variation y x hy.1 h hx.2
      linarith [le_abs_self (F x-F y)]
    · have v := variation x y hx.1 h hy.2
      linarith [neg_le_abs (F y-F x)]
  have hc : Continuous F := continuous_iff_continuousAt.2 (fun z => (hF z).continuousAt)
  have hab : a ≤ a+1 := by linarith
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (f := fun _ => F x) (g := fun t => F t+V)
    (continuous_const.intervalIntegrable _ _) ((hc.add continuous_const).intervalIntegrable _ _)
    point
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const,
    intervalIntegral.integral_const] at h
  simpa [V] using h

/-- Quadrupling physical shells makes their square roots a true geometric sum.
Summing their energies' square roots introduces no factor counting the shells. -/
theorem shell_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, (2:ℝ)^j) + 1 = 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

def energy {I : Type*} (s : Finset I) (a : I → ℝ) : ℝ :=
  Real.sqrt (∑ x ∈ s, a x ^ 2)

theorem point_le_energy {I : Type*} (s : Finset I) (a : I → ℝ) {x : I}
    (hx : x ∈ s) : |a x| ≤ energy s a := by
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact Finset.single_le_sum (fun i _ => sq_nonneg (a i)) hx

/-- Eliminate a class occurring in two distinguished arrays and any number of
additional arrays, keeping all other class indices fixed. -/
theorem eliminate_class {I J : Type*} (s : Finset I) (t : Finset J)
    (a b : I → ℝ) (v : J → I → ℝ) :
    (∑ x ∈ s, |a x| * |b x| * ∏ j ∈ t, |v j x|) ≤
      energy s a * energy s b * ∏ j ∈ t, energy s (v j) := by
  have hc : (∑ x ∈ s, |a x| * |b x|) ≤ energy s a * energy s b := by
    simpa [energy, sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt s
      (fun x => |a x|) (fun x => |b x|)
  calc
    _ ≤ ∑ x ∈ s, |a x| * |b x| * ∏ j ∈ t, energy s (v j) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => point_le_energy s (v j) hx))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ x ∈ s, |a x| * |b x|) * ∏ j ∈ t, energy s (v j) := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc
      (Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _))

/-- Exact cost of aggregating positive multiplicities in arbitrary bins.
The signal here is real; applying this to the real and imaginary parts
gives the complex version used in the paper. -/
theorem band_energy {I J : Type*} [Fintype J] [DecidableEq J]
    (s : Finset I) (bin : I → J) (m a : I → ℝ) (M : ℝ)
    (hm : ∀ i, 0 ≤ m i) (hM : ∀ j, (∑ i ∈ s with bin i=j, m i) ≤ M) :
    (∑ j, (∑ i ∈ s with bin i=j, m i*a i)^2) ≤ M * ∑ i ∈ s, m i*(a i)^2 := by
  have point (i : I) : Real.sqrt (m i) * (Real.sqrt (m i)*a i) = m i*a i := by
    rw [← mul_assoc, Real.mul_self_sqrt (hm i)]
  have bin_bound (u : Finset I) : (∑ i ∈ u, m i*a i)^2 ≤
      (∑ i ∈ u, m i) * ∑ i ∈ u, m i*(a i)^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) u
      (fun i => Real.sqrt (m i)) (fun i => Real.sqrt (m i)*a i)
    simpa only [point, mul_pow, Real.sq_sqrt (hm _)] using h
  calc
    _ ≤ ∑ j : J, M * ∑ i ∈ s with bin i=j, m i*(a i)^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact (bin_bound _).trans (mul_le_mul_of_nonneg_right (hM j)
        (Finset.sum_nonneg (fun i _ => mul_nonneg (hm i) (sq_nonneg _))))
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_fiberwise]

theorem band_budget (x L : ℝ) :
    x^11 * L^2 * L^10 = x^11 * L^12 := by
  ring


/-- A repeated label inside one slot costs at most its full two-label energy. -/
theorem diagonal_energy {I : Type*} (s : Finset I) (v : I → I → ℝ) :
    (∑ x ∈ s, (v x x)^2) ≤ ∑ x ∈ s, ∑ y ∈ s, (v x y)^2 := by
  apply Finset.sum_le_sum
  intro x hx
  exact Finset.single_le_sum (fun y _ => sq_nonneg (v x y)) hx

theorem weighted_moment {I : Type*} (s : Finset I) (a w : I → ℝ) (U : ℝ)
    (k : ℕ) (hw : ∀ x ∈ s, 0 ≤ w x) (h : ∀ x ∈ s, |a x| ≤ U) :
    (∑ x ∈ s, w x * |a x|^(k+2)) ≤ U^k * ∑ x ∈ s, w x * |a x|^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  rw [pow_add, ← mul_assoc, mul_comm (w x) _, mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (h x hx) k)
    (mul_nonneg (hw x hx) (sq_nonneg _))

/-- X = x². The two active slots have joint cost X L⁴. -/
theorem matched_budget (x L : ℝ) :
    (x^2 * L^4) * ((x^2 * L)^2 * (x^5 * L^4)) = x^11 * L^10 := by ring

/-- X = x¹⁰, so T = x⁸/L². -/
theorem inner_budget (x L : ℝ) (hL : L ≠ 0) :
    x^15 * (x^8 / L^2)^5 * L^19 = x^55 * L^9 := by field_simp; ring

section FiniteField
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The full quadratic character correlation off the diagonal. -/
theorem quadratic_shift (d : F) (hd : d ≠ 0) (hF : ringChar F ≠ 2) :
    ∑ x : F, quadraticChar F x * quadraticChar F (x-d) = -1 := by
  let e := ((Equiv.addRight (-d)).trans (Equiv.divLeft₀ d hd)).trans (Equiv.addRight 1)
  have hperm : (∑ x : F, quadraticChar F (d/(x-d)+1)) = 0 := by
    calc
      _ = ∑ x : F, quadraticChar F x :=
        Fintype.sum_equiv e _ _ (fun x => by simp [e, sub_eq_add_neg])
      _ = _ := quadraticChar_sum_zero hF
  have hterm (x : F) : quadraticChar F x * quadraticChar F (x-d) =
      quadraticChar F (d/(x-d)+1) - (if x=d then 1 else 0) := by
    by_cases hx : x=d
    · subst x
      simp
    · have hxd : x-d ≠ 0 := sub_ne_zero.mpr hx
      have he : x*(x-d)=(d/(x-d)+1)*(x-d)^2 := by field_simp; ring
      rw [if_neg hx, sub_zero, ← map_mul, he, map_mul, quadraticChar_sq_one' hxd, mul_one]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, hperm]
  simp

/-- Exact binary convolution at every output in a field where −1 is a nonsquare. -/
theorem reflected_convolution (c n : F) (hF : ringChar F ≠ 2)
    (hminus : quadraticChar F (-1) = -1) :
    (∑ x : F, quadraticChar F (x-c) * quadraticChar F (n-x-c)) =
      if n=2*c then 1-(Fintype.card F : ℤ) else 1 := by
  let d := n-2*c
  have H : (∑ x : F, quadraticChar F (x-c) * quadraticChar F (n-x-c)) =
      -(∑ z : F, quadraticChar F z * quadraticChar F (z-d)) := by
    rw [← Finset.sum_neg_distrib]
    apply Fintype.sum_equiv (Equiv.addRight (-c))
    intro x
    change quadraticChar F (x-c) * quadraticChar F (n-x-c) =
      -(quadraticChar F (x + -c) * quadraticChar F (x + -c -d))
    have he : n-x-c=(-1)*(x + -c -d) := by dsimp [d]; ring
    rw [he, map_mul, hminus, sub_eq_add_neg x c]
    ring
  rw [H]
  by_cases hn : n=2*c
  · rw [if_pos hn]
    have hd : d=0 := sub_eq_zero.mpr hn
    simp only [hd, sub_zero]
    have ht (z : F) : quadraticChar F z * quadraticChar F z =
        1 - (if z=0 then 1 else 0) := by
      by_cases hz : z=0
      · simp [hz]
      · rw [if_neg hz, sub_zero, ← pow_two, quadraticChar_sq_one hz]
    simp_rw [ht]
    rw [Finset.sum_sub_distrib]
    simp
  · rw [if_neg hn, quadratic_shift d (sub_ne_zero.mpr hn) hF]
    norm_num
end FiniteField

/-- Exact radial separation for a single smooth block of the Mellin phase. -/
theorem phase_split (t s b z x y μ : ℝ) (hz : 0 < z) (hx : 0 < x) (hy : 0 < y) :
    t*Real.log (z*x) + s*Real.log (z*y) + b*(μ/z)*(z*x+z*y-z) =
      (t+s)*Real.log z + (t*Real.log x+s*Real.log y+b*μ*(x+y-1)) := by
  rw [Real.log_mul hz.ne' hx.ne', Real.log_mul hz.ne' hy.ne']
  field_simp
  ring

end GoldbachZeroCorrelations

open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``GoldbachZeroCorrelations.unit_interval_sample, ``GoldbachZeroCorrelations.shell_sum,
      ``GoldbachZeroCorrelations.point_le_energy, ``GoldbachZeroCorrelations.eliminate_class,
      ``GoldbachZeroCorrelations.band_energy, ``GoldbachZeroCorrelations.band_budget,
      ``GoldbachZeroCorrelations.diagonal_energy, ``GoldbachZeroCorrelations.weighted_moment,
      ``GoldbachZeroCorrelations.matched_budget, ``GoldbachZeroCorrelations.inner_budget,
      ``GoldbachZeroCorrelations.quadratic_shift, ``GoldbachZeroCorrelations.reflected_convolution,
      ``GoldbachZeroCorrelations.phase_split] do
    let ax ← Lean.collectAxioms n
    unless ax.all allowed.contains do throwError "Unexpected axiom in {n}: {ax}"
    logInfo m!"{n}: {ax.qsort Name.lt |>.toList}"
