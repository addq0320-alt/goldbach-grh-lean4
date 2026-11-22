import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

/-!
# One analytic ingredient in the proposed obstruction

This is the one-step oscillation used to choose `u` in Yilin Liu, §3, (6).
We use exactly the initial values and the differential-delay equation for the
Buchstab function. No prime distribution or density asymptotic is assumed here.
-/
namespace GoldbachSpectral

open Filter Set
open scoped Topology

private theorem constant_tail_backstep {ω : ℝ → ℝ}
    (hd : ∀ t > 2, HasDerivAt ω ((ω (t-1)-ω t)/t) t) {c a : ℝ} (ha : 2 ≤ a)
    (htail : ∀ t > a, ω t = c) : ∀ x > a-1, ω x = c := by
  intro x hx
  have hxa : a < x+1 := by linarith
  have hxp : 2 < x+1 := lt_of_le_of_lt ha hxa
  have heq : ω =ᶠ[𝓝 (x+1)] (fun _ => c) := by
    filter_upwards [Ioi_mem_nhds hxa] with t ht using htail t ht
  have hz : HasDerivAt ω 0 (x+1) := heq.hasDerivAt_iff.mpr (hasDerivAt_const _ _)
  have he := (hd (x+1) hxp).unique hz
  have hsub : x+1-1 = x := by ring
  rw [hsub, htail _ hxa] at he
  exact sub_eq_zero.mp ((div_eq_zero_iff.mp he).resolve_right (by linarith))

/-- For arbitrarily large real arguments the unit-step difference is strictly positive. -/
theorem buchstab_gap_unbounded (ω : ℝ → ℝ)
    (hinit : ∀ t ∈ Ioo (1:ℝ) 2, ω t = 1/t)
    (hd : ∀ t > 2, HasDerivAt ω ((ω (t-1)-ω t)/t) t) (A : ℝ) :
    ∃ u > A, ω (u+1) < ω u := by
  by_contra! h
  let a := max A 2 + 2
  have ha : 2 ≤ a := by dsimp [a]; linarith [le_max_right A 2]
  have hAa : A+1 < a := by dsimp [a]; linarith [le_max_left A 2]
  have hanti : AntitoneOn ω (Ioi a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi a)
    · intro t ht
      exact (hd t (lt_of_le_of_lt ha ht)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : a < t := interior_subset ht
      exact (hd t (lt_of_le_of_lt ha ht')).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : a < t := interior_subset ht
      rw [(hd t (lt_of_le_of_lt ha ht')).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
      have hs := h (t-1) (by linarith)
      rw [sub_add_cancel] at hs
      linarith
  have hz : (Ioi (a+1)).EqOn (deriv ω) 0 := by
    intro t ht
    change a+1 < t at ht
    change deriv ω t = 0
    rw [(hd t (by linarith)).deriv]
    have h1 := h (t-1) (by linarith)
    rw [sub_add_cancel] at h1
    have h2 := hanti (show t-1 ∈ Ioi a by change a < t-1; linarith)
      (show t ∈ Ioi a by change a < t; linarith) (by linarith : t-1 ≤ t)
    rw [le_antisymm h1 h2, sub_self, zero_div]
  have hdiff : DifferentiableOn ℝ ω (Ioi (a+1)) := by
    intro t ht
    change a+1 < t at ht
    exact (hd t (by linarith)).differentiableAt.differentiableWithinAt
  obtain ⟨c,hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hz
  have descend (k : ℕ) : (∀ t > (k:ℝ)+2, ω t = c) → ∀ t > 1, ω t = c := by
    induction k with
    | zero =>
      intro hh
      have hb : ∀ t > (2:ℝ), ω t = c := by simpa using hh
      intro x hx
      exact constant_tail_backstep hd (le_refl (2:ℝ)) hb x (by linarith)
    | succ k ih =>
      intro hh
      apply ih
      have hb := constant_tail_backstep hd (a := ((k+1:ℕ):ℝ)+2) (by have : (0:ℝ) ≤ (k+1:ℕ) := Nat.cast_nonneg _; linarith) hh
      intro t ht
      apply hb
      push_cast; linarith
  obtain ⟨k,hk⟩ := exists_nat_gt (a+1)
  have hall := descend k (fun t ht => hc t (show a+1 < t by linarith))
  have h1 := hall (4/3) (by norm_num)
  have h2 := hall (3/2) (by norm_num)
  rw [hinit _ (by constructor <;> norm_num)] at h1
  rw [hinit _ (by constructor <;> norm_num)] at h2
  norm_num at h1 h2
  linarith

end GoldbachSpectral
