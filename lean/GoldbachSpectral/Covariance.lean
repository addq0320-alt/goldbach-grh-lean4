import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! The operator-norm step used for the truncation of the character covariance.
The Dirichlet series tail entering the right hand side is estimated analytically. -/

namespace GoldbachSpectral
open scoped InnerProductSpace BigOperators
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The rank-one map taking z to ⟪y,z⟫ x in Mathlib's convention. -/
def outer (x y : H) : H →L[ℂ] H := (innerSL ℂ y).smulRight x

private theorem outer_norm (x y : H) : ‖outer x y‖ = ‖x‖ * ‖y‖ := by
  rw [outer, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

/-- Replacing a single vector in a covariance operator. -/
theorem covariance_difference (u v : H) :
    ‖outer u u - outer v v‖ ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have hd : outer u u - outer v v = outer (u - v) u + outer v (u - v) := by
    apply ContinuousLinearMap.ext
    intro z
    change ⟪u, z⟫_ℂ • u - ⟪v, z⟫_ℂ • v =
      ⟪u, z⟫_ℂ • (u - v) + ⟪u - v, z⟫_ℂ • v
    rw [smul_sub, inner_sub_left, sub_smul]
    abel
  rw [hd]
  calc
    _ ≤ ‖outer (u - v) u‖ + ‖outer v (u - v)‖ := norm_add_le _ _
    _ = _ := by rw [outer_norm, outer_norm]; ring

/-- Applies in particular to the normalized average over the odd characters
modulo N. The bound is for the operator norm on the whole Hilbert space. -/
theorem covariance_sum_difference {ι : Type*} (s : Finset ι) (a : ι → ℂ) (u v : ι → H) :
    ‖(∑ i ∈ s, a i • outer (u i) (u i)) - (∑ i ∈ s, a i • outer (v i) (v i))‖ ≤
      ∑ i ∈ s, ‖a i‖ * ((‖u i‖ + ‖v i‖) * ‖u i - v i‖) := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_left (covariance_difference _ _) (norm_nonneg _)

end
end GoldbachSpectral
