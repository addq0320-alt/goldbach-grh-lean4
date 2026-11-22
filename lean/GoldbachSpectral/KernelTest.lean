import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# A finite-test formulation of the missing cancellation estimate

For a total family of kernel vectors, all matrix entries on finite linear
combinations suffice to certify a bound for the entire operator norm.
The two coefficient vectors are independent. A fixed finite grid, or only
entrywise bounds on the generators, would be a different hypothesis.
-/
namespace GoldbachSpectral

open scoped InnerProductSpace ComplexConjugate
noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def synth (v : ι → H) (a : ι →₀ ℂ) : H := Finsupp.linearCombination ℂ v a

/-- The finite quadratic/bilinear sums use the Mathlib inner product (linear on the right). -/
theorem finite_kernel_entry (T : H →L[ℂ] H) (v : ι → H) (a b : ι →₀ ℂ) :
    ⟪synth v a, T (synth v b)⟫_ℂ =
      ∑ i ∈ a.support, ∑ j ∈ b.support, conj (a i) * b j * ⟪v i, T (v j)⟫_ℂ := by
  classical
  simp [synth, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- No compactness, sign assumption, or diagonalization is required for this test. -/
theorem norm_le_iff_finite_tests (T : H →L[ℂ] H) (v : ι → H)
    (htotal : DenseRange (synth v)) {B : ℝ} (hB : 0 ≤ B) :
    ‖T‖ ≤ B ↔ ∀ a b : ι →₀ ℂ,
      ‖∑ i ∈ a.support, ∑ j ∈ b.support, conj (a i) * b j * ⟪v i,T (v j)⟫_ℂ‖ ≤
        B * ‖synth v a‖ * ‖synth v b‖ := by
  simp_rw [← finite_kernel_entry]
  constructor
  · intro h a b
    calc
      ‖⟪synth v a, T (synth v b)⟫_ℂ‖ ≤ ‖synth v a‖ * ‖T (synth v b)‖ := norm_inner_le_norm _ _
      _ ≤ ‖synth v a‖ * (B*‖synth v b‖) := by
        exact mul_le_mul_of_nonneg_left ((T.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right h (norm_nonneg _))) (norm_nonneg _)
      _ = _ := by ring
  · intro h
    have hall (x y : H) : ‖⟪x,T y⟫_ℂ‖ ≤ B*‖x‖*‖y‖ := by
      apply htotal.induction_on₂ (p := fun a b => ‖⟪a,T b⟫_ℂ‖ ≤ B*‖a‖*‖b‖) _ h x y
      exact isClosed_le (continuous_fst.inner (T.continuous.comp continuous_snd)).norm
        ((continuous_const.mul continuous_fst.norm).mul continuous_snd.norm)
    apply T.opNorm_le_bound hB
    intro x
    have hh := hall (T x) x
    have he : ‖⟪T x,T x⟫_ℂ‖ = ‖T x‖^2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    rw [he] at hh
    by_cases hz : ‖T x‖ = 0
    · rw [hz]; exact mul_nonneg hB (norm_nonneg _)
    · have hp := lt_of_le_of_ne (norm_nonneg (T x)) (Ne.symm hz)
      exact (mul_le_mul_iff_of_pos_left hp).mp (by nlinarith only [hh])

end
end GoldbachSpectral
