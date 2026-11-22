import GoldbachSpectral.Cancellation
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! Exact arithmetic and continuous support identities for the Li–Liu kernel.
The finite-sum theorem allows any real weight, including the product of the
von Mangoldt weights, two real tests, and the mask for units modulo N. -/

namespace GoldbachSpectral
open scoped BigOperators

private theorem opposite_iff {N m n : ℕ} (hm : 0 < m) (hmN : m < N)
    (hnN : n < N) : N ∣ m + n ↔ m + n = N := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | _ | k
    · simp at hk
      omega
    · simpa using hk
    · rw [Nat.mul_succ, Nat.mul_succ] at hk
      omega
  · intro h
    rw [h]

/-- After the diagonal is removed, the only surviving interior pairs have sum N. -/
theorem interior_signed_kernel {N m n : ℕ} (hm : 0 < m) (hmN : m < N)
    (hnN : n < N) :
    signedKernel N m n = if m + n = N then -1 else 0 := by
  simp only [signedKernel, Nat.mod_eq_of_lt hmN, Nat.mod_eq_of_lt hnN, opposite_iff hm hmN hnN]
  split_ifs <;> omega

/-- Short arithmetic truncations cancel term by term on units modulo N. -/
theorem short_signed_kernel {N X m n : ℕ} (hX : 2 * X < N) (hm : 0 < m)
    (hmX : m ≤ X) (hnX : n ≤ X) : signedKernel N m n = 0 := by
  rw [interior_signed_kernel hm (by omega) (by omega)]
  simp [show m + n ≠ N by omega]

/-- The entire weighted interior double sum equals the single reflected sum.
The two arguments of the weight need not be symmetric. -/
theorem interior_double_sum (N : ℕ) (weight : ℕ → ℕ → ℝ) :
    (∑ m ∈ Finset.Ioo 0 N, ∑ n ∈ Finset.Ioo 0 N,
      (signedKernel N m n : ℝ) * weight m n) =
      -(∑ m ∈ Finset.Ioo 0 N, weight m (N - m)) := by
  classical
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hmpos, hmN⟩ := Finset.mem_Ioo.mp hm
  have hsub : N - m ∈ Finset.Ioo 0 N := Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
  rw [Finset.sum_eq_single (N - m)]
  · rw [interior_signed_kernel hmpos hmN (Finset.mem_Ioo.mp hsub).2]
    simp [show m + (N - m) = N by omega]
  · intro n hn hne
    rw [interior_signed_kernel hmpos hmN (Finset.mem_Ioo.mp hn).2]
    simp [show m + n ≠ N by omega]
  · exact fun h => (h hsub).elim

/-- Of the three integer translates of the beta model, only reflection at
one survives on (0,1). Taking g to be the conjugate test gives the mixed form. -/
theorem interior_beta_reflection {f g : ℝ → ℂ}
    (hf : ∀ x, f x ≠ 0 → 0 < x ∧ x < 1)
    (hg : ∀ x, g x ≠ 0 → 0 < x ∧ x < 1) (u : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    f u * g (u + k) + g u * f (u + k) - f u * g ((k : ℝ) - u) =
      if k = 1 then -(f u * g (1 - u)) else 0 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have shift (a b : ℝ → ℂ) (ha : ∀ x, a x ≠ 0 → 0 < x ∧ x < 1)
      (hb : ∀ x, b x ≠ 0 → 0 < x ∧ x < 1) : a u * b (u + k) = 0 := by
    by_contra h
    obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp h
    linarith [(ha _ h₁).1, (hb _ h₂).2]
  rw [shift f g hf hg, shift g f hg hf]
  simp only [zero_add, zero_sub]
  split_ifs with h
  · subst k
    norm_num
  · have hk₂ : 2 ≤ k := by omega
    have hk₂' : (2 : ℝ) ≤ k := by exact_mod_cast hk₂
    have hzero : f u * g ((k : ℝ) - u) = 0 := by
      by_contra hn
      obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hn
      linarith [(hf _ h₁).2, (hg _ h₂).2]
    simp [hzero]

end GoldbachSpectral
