import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Finite convolution, its Haar-measure Hölder step, and the counting
arguments used in GoldbachFiveModuli.pdf. Lean and mathlib v4.19.0. -/
noncomputable section
namespace GoldbachFiveModuli
open Finset MeasureTheory
open scoped BigOperators Classical

section Convolution
variable {A : Type*} [AddCommGroup A] [Fintype A]

def correlation (F G : A → ℝ) (t : A) : ℝ := ∑ x : A, F x * G (x+t)

theorem translated_energy (F : A → ℝ) (t : A) :
    (∑ x : A, (F (x+t))^2) = ∑ x : A, (F x)^2 :=
  Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)

theorem correlation_sq (F G : A → ℝ) (t : A) :
    (correlation F G t)^2 ≤ (∑ x, (F x)^2)*(∑ x, (G x)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ F (fun x => G (x+t))
  rw [translated_energy] at h
  exact h

/-- After fixing the kernel variable the two remaining arguments are translates. -/
theorem kernel_pair_identity (K F G : A → ℝ) (t : A) :
    (∑ x : A, ∑ y : A, K (t+x-y)*(F x*G y)) =
      ∑ d : A, K d*correlation F G (t-d) := by
  calc
    _ = ∑ x : A, ∑ d : A, K d * (F x*G (x+(t-d))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Fintype.sum_equiv (Equiv.subLeft (t+x)) _ _ (fun y => by
        simp only [Equiv.subLeft_apply]
        have he : x + (t - (t + x - y)) = y := by abel
        rw [he])
    _ = _ := by rw [Finset.sum_comm]; simp [correlation, Finset.mul_sum]

theorem kernel_pair_bound (K F G : A → ℝ) (t : A) (U : ℝ)
    (hK : ∀ d, 0 ≤ K d) (hU : ∀ v, correlation F G v ≤ U) :
    (∑ x : A, ∑ y : A, K (t+x-y)*(F x*G y)) ≤ (∑ d, K d)*U := by
  rw [kernel_pair_identity, Finset.sum_mul]
  exact Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left (hU _) (hK d))

/-- The other two unrestricted slots cost their L¹ masses once the pair
bound has become uniform in their difference. -/
theorem four_slot_bound (P Q R : A → ℝ) (M : ℝ)
    (hP : ∀ x, 0 ≤ P x) (hQ : ∀ y, 0 ≤ Q y) (hR : ∀ t, R t ≤ M) :
    (∑ x : A, ∑ y : A, P x*Q y*R (x-y)) ≤
      (∑ x, P x)*(∑ y, Q y)*M := by
  calc
    _ ≤ ∑ x : A, ∑ y : A, P x*Q y*M :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (hR _) (mul_nonneg (hP x) (hQ y))))
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

end Convolution

theorem integral_pair {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (F G : T → ℝ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    (∫ t, ‖F t‖*‖G t‖ ∂μ) ≤ Real.sqrt (∫ t, ‖F t‖^2 ∂μ) *
      Real.sqrt (∫ t, ‖G t‖^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := F) (g := G)
    Real.HolderConjugate.two_two (by simpa using hF) (by simpa using hG)
  simpa [Real.sqrt_eq_rpow] using h

/-- Haar correlation at every translation, the uniform bound used before
integrating over the two unrestricted remaining frequencies in (5). -/
theorem haar_correlation {A : Type*} [AddGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (μ : Measure A) [Measure.IsAddRightInvariant μ]
    (F G : A → ℝ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (v : A) :
    (∫ x, ‖F x‖ * ‖G (x+v)‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖F x‖^2 ∂μ) * Real.sqrt (∫ x, ‖G x‖^2 ∂μ) := by
  have hp := measurePreserving_add_right μ v
  have h := integral_pair μ F (fun x => G (x+v)) hF (hG.comp_measurePreserving hp)
  have e := hp.integral_comp (MeasurableEquiv.addRight v).measurableEmbedding
    (fun x => ‖G x‖^2)
  change (∫ x, ‖G (x+v)‖^2 ∂μ) = ∫ x, ‖G x‖^2 ∂μ at e
  simpa only [e] using h

theorem physical_block_scale (B M X Z : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hX : 0 < X) (hZ : 0 < Z) :
    Real.sqrt (B*M/(X*Z))*Real.sqrt Z = Real.sqrt (B*M/X) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- Sufficient condition for the minor-arc example to have a unique
Dirichlet centre among denominators at most D. -/
theorem isolated_fraction (q s D X u : ℝ) (hq : 0 < q) (hs : 0 < s)
    (hD : 0 < D) (hX : 0 < X) (hu : 0 ≤ u) (hsD : s ≤ D)
    (h : q/D + u*q*D/X < 1) :
    1/(s*D) < 1/(q*s) - u/X := by
  have mon : u*q*s/X ≤ u*q*D/X := by gcongr
  apply (mul_lt_mul_iff_of_pos_right (mul_pos hq hs)).mp
  calc
    _ = q/D := by field_simp; ring
    _ < 1-u*q*s/X := by linarith
    _ = _ := by field_simp; ring

theorem minor_residue_scale (t : ℝ) (ht : 1 < t) :
    t ≤ t^5/(t^4-1) := by
  have hs : 0 < t^4-1 := by
    rw [show t^4-1=(t-1)*(t+1)*(t^2+1) by ring]
    have : 0 < t-1 := by linarith
    positivity
  apply (le_div_iff₀ hs).2
  nlinarith

section Shells

theorem geometric_mass (n : ℕ) : (∑ i ∈ range n, (2:ℕ)^i)+1=2^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

def shellMass (n : ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range n, min (2^i) (2^j)

theorem shell_step (n : ℕ) :
    shellMass (n+1) = shellMass n + 2*(∑ i ∈ range n, (2:ℕ)^i) + 2^n := by
  have hi : ∀ i ∈ range n, (2:ℕ)^i ≤ 2^n := by
    intro i hi
    exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt (mem_range.mp hi))
  unfold shellMass
  rw [sum_range_succ]
  simp_rw [sum_range_succ]
  rw [sum_add_distrib]
  have hl : (∑ i ∈ range n, min ((2:ℕ)^i) (2^n)) = ∑ i ∈ range n, 2^i :=
    Finset.sum_congr rfl (fun i hi' => min_eq_left (hi i hi'))
  have hr : (∑ i ∈ range n, min ((2:ℕ)^n) (2^i)) = ∑ i ∈ range n, 2^i :=
    Finset.sum_congr rfl (fun i hi' => min_eq_right (hi i hi'))
  rw [hl, hr, min_self]
  omega

/-- Exact geometric sum over both dyadic offset scales, with no logarithm. -/
theorem shell_exact (n : ℕ) : shellMass n + 2*n+3=3*2^n := by
  induction n with
  | zero => simp [shellMass]
  | succ n ih =>
    rw [shell_step, pow_succ]
    have h := geometric_mass n
    omega

theorem shell_bound (n : ℕ) : shellMass n ≤ 3*2^n := by
  have h := shell_exact n
  omega

end Shells

/-- Counting inequality for an inclusion-exclusion intersection with at
least two disjoint label equalities, when the two reference slots are fixed. -/
theorem two_reference_cases {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hca : c ≤ a) (hcb : c ≤ b) :
    (a=2 ∧ b=2 ∧ c=2) ∨ 3 ≤ 2*(a-c)+b := by omega

theorem one_reference_cases {a b c t : ℕ} (ha : a=2) (hb : 2 ≤ b)
    (hca : c ≤ a) (ht : b ≤ 2*t) (hc : 1 ≤ c) :
    (b=2 ∧ (c=1 ∨ c=2)) ∨ (3 ≤ b ∧ 2 ≤ t ∧ c ≤ 2) := by omega

/-- Two perfect pairings minus their all-equal intersection, including
multiple occurrences of an identical spectral label. -/
theorem two_pair_indicator {T : Type*} [DecidableEq T] (a b c d : T) :
    (if (a=c ∧ b=d) ∨ (a=d ∧ b=c) then (1:ℤ) else 0) =
    (if a=c ∧ b=d then 1 else 0) + (if a=d ∧ b=c then 1 else 0) -
    (if a=b ∧ b=c ∧ c=d then 1 else 0) := by
  by_cases h : a=c ∧ b=d <;> by_cases k : a=d ∧ b=c
  · obtain ⟨_, _⟩ := h; obtain ⟨_, _⟩ := k
    simp_all
  · have n : ¬(a=b ∧ b=c ∧ c=d) := by rintro ⟨rfl,rfl,rfl⟩; simp at k
    rw [if_pos (Or.inl h), if_pos h, if_neg k, if_neg n]
    norm_num
  · have n : ¬(a=b ∧ b=c ∧ c=d) := by rintro ⟨rfl,rfl,rfl⟩; simp at h
    rw [if_pos (Or.inr k), if_neg h, if_pos k, if_neg n]
    norm_num
  · have n : ¬(a=b ∧ b=c ∧ c=d) := by rintro ⟨rfl,rfl,rfl⟩; simp at h
    rw [if_neg (not_or.mpr ⟨h,k⟩), if_neg h, if_neg k, if_neg n]
    norm_num

theorem matched_log_budget (x l : ℝ) :
    (x^4*l^5)*((x^4*l)^2*(x^10*l^4)) = x^22*l^11 := by ring

theorem secondary_powers (x : ℝ) :
    (x^5)^2*x^10 = x^20 ∧ x^6*x^14=x^20 := by constructor <;> ring

theorem sixth_from_coefficients {T : Type*} (s : Finset T) (v : T → ℝ)
    (U : ℝ) (hv : ∀ i ∈ s, |v i| ≤ U) :
    (∑ i ∈ s, |v i|^6) ≤ U^4*(∑ i ∈ s, |v i|^2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ = |v i|^4*|v i|^2 := by ring
    _ ≤ _ := by gcongr; exact hv i hi

theorem pole_log_budget (x z : ℝ) (hz : z ≠ 0) :
    (x^3*z^5)^4 * (x^10/z^2) = x^22*z^18 := by field_simp; ring

theorem log_margin (L : ℝ) (h : 1 ≤ L) : L^11 ≤ L^12 := by
  calc
    L^11 = L^11*1 := (mul_one _).symm
    _ ≤ L^11*L := mul_le_mul_of_nonneg_left h (pow_nonneg (by linarith) _)
    _ = _ := by ring

end GoldbachFiveModuli

open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``GoldbachFiveModuli.translated_energy, ``GoldbachFiveModuli.correlation_sq,
    ``GoldbachFiveModuli.kernel_pair_identity, ``GoldbachFiveModuli.kernel_pair_bound,
    ``GoldbachFiveModuli.four_slot_bound, ``GoldbachFiveModuli.integral_pair,
    ``GoldbachFiveModuli.haar_correlation, ``GoldbachFiveModuli.physical_block_scale,
    ``GoldbachFiveModuli.isolated_fraction, ``GoldbachFiveModuli.minor_residue_scale,
    ``GoldbachFiveModuli.geometric_mass, ``GoldbachFiveModuli.shell_step,
    ``GoldbachFiveModuli.shell_exact, ``GoldbachFiveModuli.shell_bound,
    ``GoldbachFiveModuli.two_reference_cases, ``GoldbachFiveModuli.one_reference_cases,
    ``GoldbachFiveModuli.two_pair_indicator, ``GoldbachFiveModuli.matched_log_budget,
    ``GoldbachFiveModuli.secondary_powers, ``GoldbachFiveModuli.sixth_from_coefficients,
    ``GoldbachFiveModuli.pole_log_budget, ``GoldbachFiveModuli.log_margin]
  for n in names do
    let ax ← Lean.collectAxioms n
    unless ax.all allowed.contains do throwError "Unexpected axiom in {n}: {ax}"
    logInfo m!"{n}  {ax.qsort Name.lt |>.toList}"
