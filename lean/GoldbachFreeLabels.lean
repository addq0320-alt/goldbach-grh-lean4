import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Multiplicative character rows and matching counts used in GoldbachFreeLabels.pdf.
Lean 4.19.0, mathlib v4.19.0. Character rows may be supported on any finite
set of characters, including imprimitive characters and exclusions that have
already been fixed by the labels on the opposite side.
-/

noncomputable section
namespace GoldbachFreeLabels
open Finset
open MeasureTheory
open scoped BigOperators ComplexConjugate Classical

section Characters
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- Synthesis of a multiplicative Fourier polynomial, extended by zero on nonunits. -/
def row (s : Finset (MulChar R ℂ)) (c : MulChar R ℂ → ℂ) (a : R) : ℂ :=
  ∑ χ ∈ s, c χ * χ a

theorem orthogonal (χ ψ : MulChar R ℂ) :
    (∑ a : R, χ a * conj (ψ a)) =
      if χ=ψ then (Fintype.card Rˣ:ℂ) else 0 := by
  classical
  have hχ (a : R) : conj (ψ a) = ψ⁻¹ a := MulChar.star_apply' ψ a
  simp_rw [hχ, ← MulChar.mul_apply]
  by_cases h : χ = ψ
  · simp [h, MulChar.sum_one_eq_card_units]
  · have h' : χ*ψ⁻¹ ≠ 1 := fun e => h (mul_inv_eq_one.mp e)
    rw [if_neg h]
    exact MulChar.sum_eq_zero_of_ne_one h'

theorem coefficient_against_row (s : Finset (MulChar R ℂ)) (c : MulChar R ℂ → ℂ)
    {χ : MulChar R ℂ} (hχ : χ ∈ s) :
    (∑ a : R, χ a * conj (row s c a)) = (Fintype.card Rˣ:ℂ)*conj (c χ) := by
  classical
  calc
    _ = ∑ a : R, ∑ ψ ∈ s, conj (c ψ)*(χ a * conj (ψ a)) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [row, map_sum, map_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ψ _
      ring
    _ = ∑ ψ ∈ s, conj (c ψ)*(∑ a : R, χ a * conj (ψ a)) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by simp [orthogonal, mul_ite, hχ, mul_comm]

theorem row_energy (s : Finset (MulChar R ℂ)) (c : MulChar R ℂ → ℂ) :
    (∑ a : R, ‖row s c a‖^2) = (Fintype.card Rˣ:ℝ) * ∑ χ ∈ s, ‖c χ‖^2 := by
  have eqn : (∑ a : R, row s c a * conj (row s c a)) =
      (Fintype.card Rˣ:ℂ) * ∑ χ ∈ s, c χ*conj (c χ) := by
    calc
      _ = ∑ a : R, ∑ χ ∈ s, c χ*(χ a*conj (row s c a)) := by
        apply Finset.sum_congr rfl
        intro a _
        change (∑ χ ∈ s, c χ * χ a) * conj (row s c a) = _
        simp [Finset.sum_mul, mul_assoc]
      _ = ∑ χ ∈ s, c χ*(∑ a : R, χ a*conj (row s c a)) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [coefficient_against_row s c hχ]
        ring
  simp only [Complex.mul_conj'] at eqn
  exact_mod_cast eqn

/-- Character Parseval integrated in the offset; the measure can be normalized
Lebesgue measure on any one of the dyadic intervals in the text. -/
theorem integrated_row_energy {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (s : Finset (MulChar R ℂ)) (c : T → MulChar R ℂ → ℂ)
    (hc : ∀ χ ∈ s, Integrable (fun b => ‖c b χ‖^2) μ) :
    (∫ b, ∑ a : R, ‖row s (c b) a‖^2 ∂μ) =
      (Fintype.card Rˣ:ℝ) * ∑ χ ∈ s, ∫ b, ‖c b χ‖^2 ∂μ := by
  simp_rw [row_energy]
  rw [integral_const_mul, integral_finset_sum s hc]

/-- Two free labels can occupy the same additive numerator. -/
theorem two_rows (s t : Finset (MulChar R ℂ)) (c d : MulChar R ℂ → ℂ) :
    (∑ a : R, ‖row s c a‖ * ‖row t d a‖)^2 ≤
      (Fintype.card Rˣ:ℝ)^2 * (∑ χ ∈ s, ‖c χ‖^2) * (∑ ψ ∈ t, ‖d ψ‖^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun a => ‖row s c a‖) (fun a => ‖row t d a‖)
  rw [row_energy, row_energy] at h
  convert h using 1
  ring

omit [Fintype R] [DecidableEq R] in
theorem row_nonunit (s : Finset (MulChar R ℂ)) (c : MulChar R ℂ → ℂ)
    {a : R} (ha : ¬ IsUnit a) : row s c a = 0 := by
  simp [row, MulChar.map_nonunit _ ha]

theorem one_row (s : Finset (MulChar R ℂ)) (c : MulChar R ℂ → ℂ) :
    (∑ a : R, ‖row s c a‖)^2 ≤
      (Fintype.card Rˣ:ℝ)^2 * ∑ χ ∈ s, ‖c χ‖^2 := by
  classical
  let d : MulChar R ℂ → ℂ := fun _ => 1
  have h := two_rows s ({1}: Finset (MulChar R ℂ)) c d
  have hi (a : R) : ‖row s c a‖*‖row {1} d a‖=‖row s c a‖ := by
    by_cases ha : IsUnit a
    · simp [row, d, MulChar.one_apply ha]
    · simp [row_nonunit s c ha]
  simpa [hi, d] using h

end Characters

section Patterns
variable {α : Type*} [DecidableEq α]

/-- Multiplicity matching guarantees at least this many non-free occurrences
even when the opposite list contains repetitions. -/
theorem matches_le_known (known other : Multiset α) :
    (known ∩ other).card ≤ (other.filter (fun a => a ∈ known)).card := by
  apply Multiset.card_le_card
  apply Multiset.le_filter.mpr
  exact ⟨Multiset.inter_le_right, fun x hx => (Multiset.mem_inter.mp hx).1⟩

theorem free_count_bound (known other : Multiset α) :
    (other.filter (fun a => a ∉ known)).card ≤ other.card - (known ∩ other).card := by
  have h := matches_le_known known other
  have e := congrArg Multiset.card (Multiset.filter_add_not (fun a => a ∈ known) other)
  simp only [Multiset.card_add] at e
  omega

/-- Local count on the side with more slots, two labels per slot. -/
theorem free_count_per_modulus {small large m fixed : ℕ}
    (h : small ≤ large) (hm : m ≤ 2*small) (hr : m ≤ fixed) :
    2*large-fixed ≤ 2*(large-small)+(2*small-m) := by omega

theorem common_slots_for_three_matches {h m : ℕ} (hm : 3 ≤ m) (hc : m ≤ 2*h)
    (hh : h ≤ 3) : h=2 ∨ h=3 := by omega

end Patterns

section Estimates

/-- Cauchy--Schwarz on an arbitrary sampling measure, including the product
of normalized numerator counting measure and normalized offset measure. -/
theorem integrated_two_rows {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (F G : T → ℂ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    (∫ t, ‖F t‖ * ‖G t‖ ∂μ) ≤
      Real.sqrt (∫ t, ‖F t‖^2 ∂μ) * Real.sqrt (∫ t, ‖G t‖^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := F) (g := G)
    Real.HolderConjugate.two_two (by simpa using hF) (by simpa using hG)
  simpa [Real.sqrt_eq_rpow] using h

/-- Bounding a kernel double sum by its largest row mass. The zero counting
bound supplies the row hypothesis, with each zero carrying its multiplicity. -/
theorem kernel_row_mass {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    (K : ι → ι → ℝ) (A : ℝ) (hm : ∀ i ∈ s, 0 ≤ m i)
    (hK : ∀ i ∈ s, ∑ j ∈ s, m j * K i j ≤ A) :
    (∑ i ∈ s, ∑ j ∈ s, m i * m j * K i j) ≤ A * ∑ i ∈ s, m i := by
  calc
    _ = ∑ i ∈ s, m i * (∑ j ∈ s, m j * K i j) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i ∈ s, m i * A := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hK i hi) (hm i hi)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- The two rows can share the whole sampling point (numerator and offset).
The measure is a general finite positive weight on that sampling space. -/
theorem two_rows_weighted {ι : Type*} (s : Finset ι) (w F G : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * F i * G i)^2 ≤
      (∑ i ∈ s, w i * (F i)^2) * (∑ i ∈ s, w i * (G i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) s
    (fun i => Real.sqrt (w i) * F i) (fun i => Real.sqrt (w i) * G i)
  have h1 (i) (hi : i ∈ s) :
      Real.sqrt (w i) * F i * (Real.sqrt (w i) * G i) = w i * F i * G i := by
    calc
      _ = (Real.sqrt (w i))^2 * F i * G i := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i hi)]
  have h2 (A : ι → ℝ) (i) (hi : i ∈ s) :
      (Real.sqrt (w i) * A i)^2 = w i * (A i)^2 := by
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl (h2 F),
    Finset.sum_congr rfl (h2 G)] at h
  exact h

/-- Sum over full anchor residue rows, with all the complementary data fixed. -/
theorem translated_grid {G H : Type*} [AddGroup G] [AddGroup H]
    (f : G →+ H) (hf : Function.Surjective f) (b c : H) :
    Nat.card (f ⁻¹' ({b}:Set H)) = Nat.card (f ⁻¹' ({c}:Set H)) :=
  Nat.card_congr (AddMonoidHom.fiberEquivOfSurjective hf b c)

theorem one_more_period {k x length : ℝ} (hk : 0 < k) (hx : 0 < x)
    (hb : 0 < length) :
    (length/x+1/k)/(length/x) = 1+x/(k*length) := by
  field_simp
  ring

/-- Integrating the longest anchor interval trades one frequency scale for the
smallest anchor modulus; the statement applies to each anchor individually. -/
theorem anchor_envelope {q b H S : ℝ} (hq : 0 ≤ q) (hb : 0 < b)
    (hS : b ≤ S) (hH : q*b ≤ H) : (q*b)^2/S ≤ H*q := by
  apply (div_le_iff₀ (lt_of_lt_of_le hb hS)).2
  have hh : 0 ≤ H := le_trans (mul_nonneg hq hb.le) hH
  calc
    _ = (q*b)*q*b := by ring
    _ ≤ H*q*b := by gcongr
    _ ≤ H*q*S := mul_le_mul_of_nonneg_left hS (mul_nonneg hh hq)

theorem squared_modulus_gain {q b H : ℝ} (hq : 0 ≤ q)
    (h : q*b ≤ H) : (Real.sqrt q*b)*Real.sqrt q ≤ H := by
  calc
    _ = (Real.sqrt q)^2*b := by ring
    _ = q*b := by rw [Real.sq_sqrt hq]
    _ ≤ H := h

/-- x = X^(1/4) so that sqrt(X) = x^2. The two four-match contributions
both have exponent 5; with three matches the larger one has exponent 21/4. -/
theorem four_match_powers (x : ℝ) :
    (x^2)^8*(x^2)^2 = x^20 ∧ x^4*(x^2)^8=x^20 := by constructor <;> ring

theorem three_match_powers (x : ℝ) :
    (x^2)^9*x^3=x^21 ∧ x^4*(x^2)^8*x=x^21 := by constructor <;> ring

/-- x = X^(1/4); a free row after averaging both numerator and offset costs x. -/
theorem joint_match_powers (x : ℝ) :
    ((x^2)^4*x^4)*x^8=x^20 ∧ ((x^2)^4*x^5)*x^8=x^21 ∧
    ((x^2)^6*x^2)*x^6=x^20 ∧ ((x^2)^6*x^3)*x^6=x^21 := by
  constructor <;> [ring; constructor <;> [ring; constructor <;> ring]]

/-- In the balanced case the number of active distinct moduli is 1, 2, or 3. -/
theorem balanced_sparse_powers (x : ℝ) :
    x^13*x^8=x^21 ∧ x^14*x^6=x^20 ∧ x^15*x^6=x^21 := by
  constructor <;> [ring; constructor <;> ring]

theorem margin_at_target : (5:ℚ) < 11/2 ∧ (21:ℚ)/4 < 11/2 := by norm_num

end Estimates
end GoldbachFreeLabels

open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``GoldbachFreeLabels.orthogonal, ``GoldbachFreeLabels.coefficient_against_row,
    ``GoldbachFreeLabels.row_energy, ``GoldbachFreeLabels.integrated_row_energy,
    ``GoldbachFreeLabels.integrated_two_rows, ``GoldbachFreeLabels.two_rows, ``GoldbachFreeLabels.row_nonunit,
    ``GoldbachFreeLabels.one_row, ``GoldbachFreeLabels.matches_le_known,
    ``GoldbachFreeLabels.free_count_bound, ``GoldbachFreeLabels.free_count_per_modulus,
    ``GoldbachFreeLabels.common_slots_for_three_matches, ``GoldbachFreeLabels.kernel_row_mass,
    ``GoldbachFreeLabels.two_rows_weighted, ``GoldbachFreeLabels.translated_grid,
    ``GoldbachFreeLabels.one_more_period, ``GoldbachFreeLabels.anchor_envelope,
    ``GoldbachFreeLabels.squared_modulus_gain, ``GoldbachFreeLabels.four_match_powers,
    ``GoldbachFreeLabels.three_match_powers, ``GoldbachFreeLabels.joint_match_powers,
    ``GoldbachFreeLabels.balanced_sparse_powers, ``GoldbachFreeLabels.margin_at_target]
  for n in names do
    let deps ← Lean.collectAxioms n
    unless deps.all allowed.contains do
      throwError "Unexpected axiom in {n}: {deps}"
    logInfo m!"{n}  {deps.qsort Name.lt |>.toList}"
