import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-!
# Exact cancellation on one side of the midpoint

The arithmetic statement is about the congruence kernel after diagonal
subtraction. The real-variable statement is about the three translates in the
Beta model at integer scales. Neither requires GRH or information on primes.
-/
namespace GoldbachSpectral

/-- The lower and upper open halves of the physical interval `(0,1)`. -/
inductive Side | lower | upper

def OnSide : Side → ℝ → Prop
  | .lower, x => 0 < x ∧ x < 1/2
  | .upper, x => 1/2 < x ∧ x < 1

private theorem in_unit {s : Side} {x : ℝ} (hx : OnSide s x) : 0 < x ∧ x < 1 := by
  cases s <;> simp only [OnSide] at hx <;> constructor <;> linarith [hx.1,hx.2]

/-- No sum on one open half is an integer. The fact that the shift is an integer
also rules out all sums in `(1,2)` on the upper half. -/
theorem same_side_sum_ne_nat {s : Side} {x y : ℝ} (hx : OnSide s x) (hy : OnSide s y)
    (k : ℕ) : x+y ≠ (k:ℝ) := by
  rcases k with _ | k
  · have h1 := (in_unit hx).1; have h2 := (in_unit hy).1
    push_cast; linarith
  · cases s <;> simp only [OnSide] at hx hy
    · have hk : (1:ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      linarith [hx.2,hy.2]
    · rcases k with _ | k
      · push_cast; linarith [hx.1,hy.1]
      · have hk : (2:ℝ) ≤ (k+1+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
        linarith [hx.2,hy.2]

private theorem translate_term_zero {s : Side} {f g : ℝ → ℝ}
    (hf : ∀ x, f x ≠ 0 → OnSide s x) (hg : ∀ x, g x ≠ 0 → OnSide s x)
    (u : ℝ) {k : ℕ} (hk : 1 ≤ k) : f u * g (u+k) = 0 := by
  by_contra h
  obtain ⟨hu,hv⟩ := mul_ne_zero_iff.mp h
  have ha := (in_unit (hf u hu)).1
  have hb := (in_unit (hg _ hv)).2
  have hc : (1:ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- Pointwise vanishing of the integer-scale Beta integrand, so its integrals
and their weighted sums vanish whenever the two weights occupy the same side. -/
theorem same_side_beta_zero {s : Side} {f g : ℝ → ℝ}
    (hf : ∀ x, f x ≠ 0 → OnSide s x) (hg : ∀ x, g x ≠ 0 → OnSide s x)
    (u : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    f u * g (u+k) + g u * f (u+k) - f u * g ((k:ℝ)-u) = 0 := by
  have hrefl : f u * g ((k:ℝ)-u) = 0 := by
    by_contra h
    obtain ⟨hu,hv⟩ := mul_ne_zero_iff.mp h
    exact same_side_sum_ne_nat (hf _ hu) (hg _ hv) k (by linarith)
  rw [translate_term_zero hf hg u hk, translate_term_zero hg hf u hk, hrefl]; norm_num

/-- The signed congruence kernel from odd-character orthogonality after subtracting
its exact diagonal, evaluated on integer test pairs. Multiplication by any weights,
including the von Mangoldt weights on units, preserves a zero entry. -/
def signedKernel (N m n : ℕ) : ℤ :=
  (if m % N = n % N then 1 else 0) - (if N ∣ m+n then 1 else 0) -
    (if m = n then 1 else 0)

theorem same_side_arithmetic_zero {s : Side} {N m n : ℕ} (hN : 0 < N)
    (hm : OnSide s ((m:ℝ)/N)) (hn : OnSide s ((n:ℝ)/N)) : signedKernel N m n = 0 := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hm' : m < N := by
    have hh := (div_lt_one hN').mp (in_unit hm).2
    exact_mod_cast hh
  have hn' : n < N := by
    have hh := (div_lt_one hN').mp (in_unit hn).2
    exact_mod_cast hh
  have hd : ¬ N ∣ m+n := by
    rintro ⟨k,hk⟩
    apply same_side_sum_ne_nat hm hn k
    rw [← add_div, div_eq_iff hN'.ne']
    exact_mod_cast (hk.trans (Nat.mul_comm N k))
  simp [signedKernel, Nat.mod_eq_of_lt hm', Nat.mod_eq_of_lt hn', hd]

end GoldbachSpectral
