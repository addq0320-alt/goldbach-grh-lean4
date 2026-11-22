import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Supporting lemmas for the square-root exceptional-set argument.
Lean 4.19.0 with Mathlib v4.19.0:
`lake env lean --trust=0 -DwarningAsError=true GoldbachFarey.lean`

The analytic GRH bounds on sums over primes and the Hardy-space
identification are inputs proved or cited in the accompanying paper.
-/
namespace GoldbachFarey
open MeasureTheory
open scoped BigOperators Interval

section Characters
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Convolution over one complete period. Different frequencies cancel. -/
theorem frequency_pair (χ ψ : AddChar G ℂ) (n : G) :
    (∑ m : G, χ m * ψ (n - m)) =
      if χ = ψ then (Fintype.card G : ℂ) * χ n else 0 := by
  classical
  calc
    _ = ∑ m : G, (χ - ψ) m * ψ n := by
      apply Finset.sum_congr rfl
      intro m _
      rw [sub_eq_add_neg n m, AddChar.map_add_eq_mul, AddChar.sub_apply]
      ring
    _ = (∑ m : G, (χ - ψ) m) * ψ n := (Finset.sum_mul ..).symm
    _ = _ := by
      by_cases he : χ = ψ
      · subst ψ
        simp
      · simp [AddChar.sum_eq_ite, he, sub_ne_zero.mpr he]

/-- The only frequencies in two finite Ramanujan-type sums contributing to
the period average of their additive convolution are the common frequencies. -/
theorem frequency_sets (S T : Finset (AddChar G ℂ)) (n : G) :
    (∑ m : G, (∑ χ ∈ S, χ m) * (∑ ψ ∈ T, ψ (n - m))) =
      ∑ χ ∈ S, if χ ∈ T then (Fintype.card G : ℂ) * χ n else 0 := by
  classical
  calc
    _ = ∑ m : G, ∑ χ ∈ S, ∑ ψ ∈ T, χ m * ψ (n - m) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ χ ∈ S, ∑ ψ ∈ T, ∑ m : G, χ m * ψ (n - m) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      simp_rw [frequency_pair]
      simp
end Characters

/-- Subtract two finite models in a correlation. The two mixed sums and
the pure model have the same predicted value; their errors and the tail
of that prediction add. For the Goldbach problem, take the index to be m,
the second weight at N-m and the models to be the two values of P_R. -/
theorem residual_correlation {ι : Type*} (s : Finset ι) (f g p q : ι → ℝ)
    {model main A B C T : ℝ}
    (h₁ : |(∑ i ∈ s, f i * q i) - model| ≤ A)
    (h₂ : |(∑ i ∈ s, p i * g i) - model| ≤ B)
    (h₃ : |(∑ i ∈ s, p i * q i) - model| ≤ C)
    (htail : |model - main| ≤ T) :
    |(∑ i ∈ s, f i * g i) - main - ∑ i ∈ s, (f i - p i)*(g i - q i)| ≤
      A+B+C+T := by
  have expand : (∑ i ∈ s, (f i-p i)*(g i-q i)) =
      (∑ i ∈ s, f i*g i) - (∑ i ∈ s, f i*q i) -
      (∑ i ∈ s, p i*g i) + ∑ i ∈ s, p i*q i := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [expand, abs_le]
  rw [abs_le] at h₁ h₂ h₃ htail
  constructor <;> linarith only [h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2, htail.1, htail.2]

private theorem product_error {f g j k : ℂ} {D : ℝ}
    (h₁ : ‖f - j‖ ≤ D) (h₂ : ‖g - k‖ ≤ D) :
    ‖f*g-j*k‖^2 ≤ 2*D^2*(‖g‖^2+‖j‖^2) := by
  have h : ‖f*g-j*k‖ ≤ D*(‖g‖+‖j‖) := by
    calc
      _ = ‖(f-j)*g + j*(g-k)‖ := by congr 1; ring
      _ ≤ ‖(f-j)*g‖ + ‖j*(g-k)‖ := norm_add_le _ _
      _ = ‖f-j‖*‖g‖ + ‖j‖*‖g-k‖ := by rw [norm_mul, norm_mul]
      _ ≤ D*‖g‖ + ‖j‖*D := add_le_add
        (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _))
        (mul_le_mul_of_nonneg_left h₂ (norm_nonneg _))
      _ = _ := by ring
  calc
    _ ≤ (D*(‖g‖+‖j‖))^2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ _ := by nlinarith only [sq_nonneg (D*(‖g‖-‖j‖))]

/-- The circle-method product estimate in L². Integrability of the error
is derived from the pointwise approximation and the two input energies. -/
theorem circle_product_energy {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (F G J K : T → ℂ) (hf : Measurable F) (hg : Measurable G)
    (hj : Measurable J) (hk : Measurable K) {D : ℝ}
    (h₁ : ∀ x, ‖F x - J x‖ ≤ D) (h₂ : ∀ x, ‖G x - K x‖ ≤ D)
    (hG : Integrable (fun x => ‖G x‖^2) μ)
    (hJ : Integrable (fun x => ‖J x‖^2) μ) :
    (∫ x, ‖F x*G x-J x*K x‖^2 ∂μ) ≤
      2*D^2*((∫ x, ‖G x‖^2 ∂μ) + (∫ x, ‖J x‖^2 ∂μ)) := by
  have hu : Integrable (fun x => 2*D^2*(‖G x‖^2+‖J x‖^2)) μ :=
    (hG.add hJ).const_mul _
  have hd : Integrable (fun x => ‖F x*G x-J x*K x‖^2) μ := by
    apply hu.mono' ((((hf.mul hg).sub (hj.mul hk)).norm.pow_const 2).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact product_error (h₁ x) (h₂ x)
  calc
    _ ≤ ∫ x, 2*D^2*(‖G x‖^2+‖J x‖^2) ∂μ :=
      integral_mono hd hu (fun x => product_error (h₁ x) (h₂ x))
    _ = _ := by rw [integral_const_mul, integral_add hG hJ]

/-- Rescaling the variable cutoff gives precisely the third inverse power. -/
theorem rescale_prefix_energy (error : ℝ → ℝ) {N a b : ℝ} (hN : N ≠ 0) :
    N⁻¹^2 * (∫ u in a..b, (error (N*u))^2) =
      N⁻¹^3 * (∫ y in N*a..N*b, (error y)^2) := by
  rw [intervalIntegral.integral_comp_mul_left (fun y => (error y)^2) hN]
  simp only [smul_eq_mul]
  ring

/-- Transfer a fixed-cutoff second moment on [0,2X] to the moving cutoffs
n*u, with the normalization appearing in the Hilbert--Schmidt estimate. -/
theorem dyadic_cutoff_moment (s : Finset ℕ) (error : ℕ → ℝ → ℝ)
    {X a b : ℝ} (hX : 0 < X) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hr : ∀ n ∈ s, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*X)
    (hi : ∀ n ∈ s, IntegrableOn (fun y => (error n y)^2) (Set.Ioc 0 (2*X))) :
    (∑ n ∈ s, (n : ℝ)⁻¹^2 * ∫ u in a..b, (error n (n*u))^2) ≤
      X⁻¹^3 * ∫ y in (0 : ℝ)..(2*X), ∑ n ∈ s, (error n y)^2 := by
  have hH : 0 ≤ 2*X := by linarith
  calc
    _ ≤ ∑ n ∈ s, X⁻¹^3 * ∫ y in (0 : ℝ)..(2*X), (error n y)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hx, nh⟩ := hr n hn
      have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le hX hx
      have hna : (n:ℝ)*a ≤ n*b := mul_le_mul_of_nonneg_left hab hnpos.le
      have hnb : (n:ℝ)*b ≤ 2*X := (mul_le_of_le_one_right hnpos.le hb).trans nh
      rw [rescale_prefix_energy (error n) hnpos.ne',
        intervalIntegral.integral_of_le hna, intervalIntegral.integral_of_le hH]
      apply mul_le_mul
      · exact pow_le_pow_left₀ (inv_nonneg.mpr hnpos.le) ((inv_le_inv₀ hnpos hX).mpr hx) 3
      · exact setIntegral_mono_set (hi n hn)
          (Filter.Eventually.of_forall fun y => sq_nonneg (error n y))
          (Filter.Eventually.of_forall fun _ hy =>
            ⟨lt_of_le_of_lt (mul_nonneg hnpos.le ha) hy.1, hy.2.trans hnb⟩)
      · exact integral_nonneg fun y => sq_nonneg (error n y)
      · exact pow_nonneg (inv_nonneg.mpr hX.le) _
    _ = _ := by
      simp only [intervalIntegral.integral_of_le hH, integral_finset_sum s hi, Finset.mul_sum]

/-- On the normalized interval measure, subtracting the mean gives the
least squared distance to a constant in the single-modulus criterion. -/
theorem centered_energy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ)
    (hf₂ : Integrable (fun x => (f x)^2) μ) (c : ℝ) :
    (∫ x, (f x-c)^2 ∂μ) =
      (∫ x, (f x-(∫ y, f y ∂μ))^2 ∂μ) + (c-(∫ y, f y ∂μ))^2 := by
  have expand (b : ℝ) : (∫ x, (f x-b)^2 ∂μ) =
      (∫ x, (f x)^2 ∂μ) - (2*b)*(∫ x, f x ∂μ) + b^2 := by
    have id : (fun x => (f x-b)^2) = fun x => ((f x)^2 - (2*b)*(f x)) + b^2 := by
      funext x
      ring
    have hq : Integrable (fun x => (2*b)*f x) μ := hf.const_mul (2*b)
    have hd : Integrable (fun x => (f x)^2-(2*b)*f x) μ := hf₂.sub hq
    have hc : Integrable (fun _ : Ω => b^2) μ := integrable_const _
    rw [id, integral_add hd hc, integral_sub hf₂ hq, integral_const_mul]
    simp
  rw [expand c, expand (∫ y, f y ∂μ)]
  ring

/-- A second moment for squared Hilbert--Schmidt norms controls the number of
operator norms exceeding a threshold proportional to the singular series.
Here `energy n` may be any upper bound for the squared operator norm. -/
theorem exceptional_count {ι : Type*} (s : Finset ι) (defect scale energy : ι → ℝ)
    {t s₀ M : ℝ} (ht : 0 < t) (hs₀ : 0 < s₀)
    (hscale : ∀ n ∈ s, s₀ ≤ scale n)
    (hdom : ∀ n ∈ s, (defect n)^2 ≤ energy n)
    (hm : ∑ n ∈ s, energy n ≤ M) :
    ((s.filter fun n => t * scale n < defect n).card : ℝ) ≤ M / (t*s₀)^2 := by
  classical
  let bad := s.filter fun n => t * scale n < defect n
  have hsub : bad ⊆ s := Finset.filter_subset _ _
  apply (le_div_iff₀ (pow_pos (mul_pos ht hs₀) 2)).mpr
  change (bad.card : ℝ) * (t*s₀)^2 ≤ M
  calc
    _ = ∑ _n ∈ bad, (t*s₀)^2 := by simp
    _ ≤ ∑ n ∈ bad, energy n := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hs, hd⟩ := Finset.mem_filter.mp hn
      have hw : t*s₀ ≤ defect n :=
        (mul_le_mul_of_nonneg_left (hscale n hs) ht.le).trans hd.le
      exact (pow_le_pow_left₀ (mul_pos ht hs₀).le hw 2).trans (hdom n hs)
    _ ≤ ∑ n ∈ s, energy n := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn _ => (sq_nonneg (defect n)).trans (hdom n hn))
    _ ≤ M := hm

end GoldbachFarey

open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``GoldbachFarey.frequency_pair, ``GoldbachFarey.frequency_sets,
    ``GoldbachFarey.residual_correlation, ``GoldbachFarey.circle_product_energy,
    ``GoldbachFarey.rescale_prefix_energy,
    ``GoldbachFarey.dyadic_cutoff_moment, ``GoldbachFarey.centered_energy,
    ``GoldbachFarey.exceptional_count]
  for name in names do
    let deps ← Lean.collectAxioms name
    unless deps.all allowed.contains do
      throwError "Unexpected axiom in {name}: {deps}"
    logInfo m!"{name}  {deps.qsort Name.lt |>.toList}"
