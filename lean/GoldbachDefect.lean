import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Three transfer lemmas in the proof for the balanced Goldbach compression.
Check with Lean 4.19.0 and Mathlib v4.19.0 using
`lake env lean --trust=0 -DwarningAsError=true GoldbachDefect.lean`.
The analytic estimates on the circle and the identification with the arithmetic
operator are supplied in the accompanying proof, not as axioms in this file.
-/
namespace GoldbachDefect
open Filter Set
open scoped Topology BigOperators

/-- Uniform norm control on a compact test class follows from pointwise
convergence there and a uniform Lipschitz bound for the discrepancy functionals. -/
theorem uniform_on_compact_tests {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (hK : IsCompact K) (F : ℕ → E → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ n, ∀ x ∈ K, ∀ y ∈ K, dist (F n x) (F n y) ≤ C * dist x y)
    (hPoint : ∀ x ∈ K, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ K, ‖F n x‖ < ε := by
  intro ε hε
  let r := ε / (2 * (C + 1))
  have hpos : 0 < C + 1 := by linarith
  have hr : 0 < r := div_pos hε (by positivity)
  have hscale : (C + 1) * r = ε / 2 := by
    dsimp [r]
    field_simp [ne_of_gt hpos]
    ring
  obtain ⟨T, hTK, hfin, hcover⟩ := finite_cover_balls_of_compact hK hr
  have hnet : ∀ᶠ n in atTop, ∀ y ∈ T, ‖F n y‖ < ε / 2 := by
    apply hfin.eventually_all.mpr
    intro y hy
    simpa using Metric.tendsto_nhds.mp (hPoint y (hTK hy)) (ε / 2) (half_pos hε)
  filter_upwards [hnet] with n hn
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hcover hx)
  obtain ⟨hyT, hxy⟩ := Set.mem_iUnion.mp hy
  have hd : dist x y < r := Metric.mem_ball.mp hxy
  have h₁ := mul_lt_mul_of_pos_left hd hpos
  have h₂ := hLip n x hx y (hTK hyT)
  have h₃ := hn y hyT
  have h₄ : ‖F n x‖ ≤ dist (F n x) (F n y) + ‖F n y‖ := by
    simpa using dist_triangle (F n x) (F n y) 0
  have hdx : 0 ≤ dist x y := dist_nonneg
  nlinarith

/-- Two endpoint errors and the increment of the main term control every
intermediate cutoff of a nondecreasing arithmetic count. -/
theorem monotone_cutoff_error (count main : ℝ → ℝ) (hc : Monotone count)
    (hm : Monotone main) {u y v err step : ℝ} (hu : u ≤ y) (hv : y ≤ v)
    (hstep : main v - main u ≤ step)
    (hleft : |count u - main u| ≤ err) (hright : |count v - main v| ≤ err) :
    |count y - main y| ≤ err + step := by
  obtain ⟨hl, _⟩ := abs_le.mp hleft
  obtain ⟨_, hr⟩ := abs_le.mp hright
  apply abs_le.mpr
  constructor <;> linarith [hc hu, hc hv, hm hu, hm hv]

/-- The union, over grid cutoffs, of exceptional integers for a complex coefficient. -/
noncomputable def badIndices {ι : Type*} (grid : Finset ι) (indices : Finset ℕ)
    (coeff : ι → ℕ → ℂ) (t : ℝ) : Finset ℕ := by
  classical
  exact indices.filter (fun n => ∃ j ∈ grid, t ≤ ‖coeff j n‖)

/-- A finite second-moment estimate bounds the actual union of bad sets, with
the grid outside the absolute value. No independence is needed. -/
theorem exceptional_card_sq {ι : Type*} (grid : Finset ι) (indices : Finset ℕ)
    (coeff : ι → ℕ → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ((badIndices grid indices coeff t).card : ℝ) * t^2 ≤
      ∑ n ∈ indices, ∑ j ∈ grid, ‖coeff j n‖^2 := by
  classical
  let bad := badIndices grid indices coeff t
  change (bad.card : ℝ) * t^2 ≤ _
  have hsub : bad ⊆ indices := Finset.filter_subset _ _
  calc
    _ = ∑ _n ∈ bad, t^2 := by simp
    _ ≤ ∑ n ∈ bad, ∑ j ∈ grid, ‖coeff j n‖^2 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨j, hj, hval⟩ := (Finset.mem_filter.mp hn).2
      exact (pow_le_pow_left₀ ht hval 2).trans
        (Finset.single_le_sum (fun k _ => sq_nonneg ‖coeff k n‖) hj)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖coeff j n‖))

end GoldbachDefect

open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``GoldbachDefect.uniform_on_compact_tests,
    ``GoldbachDefect.monotone_cutoff_error, ``GoldbachDefect.exceptional_card_sq]
  for name in names do
    let deps ← Lean.collectAxioms name
    unless deps.all allowed.contains do
      throwError "Unexpected axiom in {name}: {deps}"
    logInfo m!"{name}  {deps.qsort Name.lt |>.toList}"
