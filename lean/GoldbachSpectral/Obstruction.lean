import GoldbachSpectral.Product
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp

/-!
# What a large norm implies, and which widths can survive

`δ₂` means δ squared. We keep the singular series, eigenvalues and norm as
parameters. The arithmetic large-norm lower bound is an explicit hypothesis
of `obstruction_arbitrarily_large`, not a theorem about primes proved here.
-/

namespace GoldbachSpectral

open Filter
open scoped Quaternion
noncomputable section

def weights (δ₂ : ℝ) (μ : ℕ → ℝ) (j : ℕ) : ℝ := (4/δ₂) * (μ j)^2

def deltaSq (n s : ℝ) : ℝ := s * (Real.log n)^3 / n

theorem weights_summable {μ : ℕ → ℝ} (hs : Summable fun j => (μ j)^2) (δ₂ : ℝ) :
    Summable (weights δ₂ μ) := hs.mul_left _

/-- Applies to a compact self-adjoint spectrum once `m` is its attained absolute maximum. -/
theorem norm_dictionary {μ : ℕ → ℝ} (hs : Summable fun j => (μ j)^2)
    {m δ₂ η : ℝ} (hδ : 0 < δ₂) (hη : 0 < η) (hhalf : η ≤ 1/2)
    (hbound : ∀ j, |μ j| ≤ m) (hmax : ∃ j, |μ j| = m) :
    ZeroFree (weights δ₂ μ) η ↔ 4 * m^2 * (η*(1-η)) ≤ δ₂ := by
  have hb : ∀ j, 0 ≤ weights δ₂ μ j := fun j => by unfold weights; positivity
  rw [zeroFree_iff (weights_summable hs δ₂) hb hη hhalf]
  have hconv (j : ℕ) : weights δ₂ μ j * (η*(1-η)) ≤ 1 ↔
      4 * (μ j)^2 * (η*(1-η)) ≤ δ₂ := by
    unfold weights
    rw [show 4 / δ₂ * (μ j)^2 * (η*(1-η)) = 4 * (μ j)^2 * (η*(1-η)) / δ₂ by ring,
      div_le_one hδ]
  constructor
  · intro h
    obtain ⟨j,hj⟩ := hmax
    rw [← hj, sq_abs]
    exact (hconv j).mp (h j)
  · intro h j
    apply (hconv j).mpr
    have hsq : (μ j)^2 ≤ m^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbound j) 2
    have hnonneg : 0 ≤ η*(1-η) := mul_nonneg hη.le (by linarith)
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith : 4*(μ j)^2 ≤ 4*m^2) hnonneg) h

/-- Already the preprint's exponent `D=2` suffices to violate R once `s ≤ log n`. -/
theorem log_square_refutes_R {n s : ℝ} (hn : 0 < n) (hL : 0 < Real.log n)
    (hs : 0 < s) (hsL : s ≤ Real.log n) {μ : ℕ → ℝ}
    (hsum : Summable fun j => (μ j)^2) {j : ℕ}
    (hpeak : (Real.log n)^2 < Real.sqrt n * |μ j|) :
    ∃ x : ℝ, 1/2 < x ∧ IsZero (weights (deltaSq n s) μ) (x : ℍ[ℝ]) := by
  have hsq := mul_self_lt_mul_self (sq_nonneg (Real.log n)) hpeak
  have hid : (Real.sqrt n * |μ j|) * (Real.sqrt n * |μ j|) = n*(μ j)^2 := by
    rw [← pow_two, mul_pow, Real.sq_sqrt hn.le, sq_abs]
  rw [hid] at hsq
  have hb : s*(Real.log n)^3 < n*(μ j)^2 := calc
    s*(Real.log n)^3 ≤ (Real.log n)*(Real.log n)^3 :=
      mul_le_mul_of_nonneg_right hsL (by positivity)
    _ = (Real.log n)^2 * (Real.log n)^2 := by ring
    _ < _ := hsq
  have hδ : 0 < deltaSq n s := by unfold deltaSq; positivity
  have hw : 4 < weights (deltaSq n s) μ j := by
    unfold weights
    rw [show 4 / deltaSq n s * (μ j)^2 = (4*(μ j)^2) / deltaSq n s by ring, lt_div_iff₀ hδ]
    unfold deltaSq
    rw [← mul_div_assoc, div_lt_iff₀ hn]
    nlinarith only [hb]
  have hfail : 1 < weights (deltaSq n s) μ j * (1/2*(1-1/2)) := by linarith
  obtain ⟨x,hx,hz⟩ := right_real_zero_of_weight (weights_summable hsum _) (by norm_num) hfail
  exact ⟨x,by linarith,hz⟩

/-- Use IVT to obtain an actual real zero in the prohibited open half-space. -/
theorem spike_gives_real_zero {n s B : ℝ} (hn : 0 < n) (hL : 4 ≤ Real.log n)
    (hs : 0 < s) (hsL : s ≤ Real.log n) (hB : 2 ≤ B)
    {μ : ℕ → ℝ} (hsum : Summable fun j => (μ j)^2) {j : ℕ}
    (hspike : B * (Real.log n)^3 < Real.sqrt n * |μ j|) :
    ∃ x : ℝ, 1-1/B < x ∧ IsZero (weights (deltaSq n s) μ) (x : ℍ[ℝ]) := by
  let L := Real.log n
  let A := Real.sqrt n * |μ j|
  change B * L^3 < A at hspike
  have hL4 : 4 ≤ L := hL
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  have hL2 : 1 ≤ L^2 := one_le_pow₀ (by linarith)
  have hLc : L ≤ L^3 := by nlinarith [mul_le_mul_of_nonneg_right hL2 hL0.le]
  have hLB : L ≤ B * L^3 := hLc.trans (le_mul_of_one_le_left (by positivity) (by linarith))
  have hAs : s ≤ A := hsL.trans (hLB.trans hspike.le)
  have hA : 0 < A := hs.trans_le hAs
  have hbig : B * (s*L^3) < A^2 := calc
    B * (s*L^3) = (B*L^3)*s := by ring
    _ < A*s := mul_lt_mul_of_pos_right hspike hs
    _ ≤ A*A := mul_le_mul_of_nonneg_left hAs hA.le
    _ = A^2 := by ring
  have hAsq : A^2 = n*(μ j)^2 := by
    dsimp [A]; rw [mul_pow, Real.sq_sqrt hn.le, sq_abs]
  have hden : 0 < s * L^3 := by positivity
  have hw : 4*B < weights (deltaSq n s) μ j := calc
    4*B < 4*A^2 / (s*L^3) := (lt_div_iff₀ hden).2 (by nlinarith only [hbig])
    _ = weights (deltaSq n s) μ j := by
      rw [hAsq]; unfold weights deltaSq
      field_simp [hn.ne',hs.ne',hL0.ne',L]; ring
  have hη : 0 < 1/B := by positivity
  have hηhalf : 1/B ≤ 1/2 := (div_le_div_iff₀ hB0 (by norm_num : (0:ℝ)<2)).2 (by linarith)
  have hpos : 0 < 1/B*(1-1/B) := mul_pos hη (by linarith)
  apply right_real_zero_of_weight (weights_summable hsum _) hη (j := j)
  calc
    1 ≤ 4*(1-1/B) := by linarith
    _ = 4*B*(1/B*(1-1/B)) := by field_simp; ring
    _ < _ := mul_lt_mul_of_pos_right hw hpos

/-- The preprint's arbitrarily large norm spikes (natural exponents suffice), together with
an attained spectral maximum, exclude *every fixed inverse-log-power width* at arbitrarily
large even moduli. Each witness is a real quaternion strictly inside the excluded region. -/
theorem obstruction_arbitrarily_large (s m : ℕ → ℝ) (μ : ℕ → ℕ → ℝ)
    (hsum : ∀ n, Even n → Summable fun j => (μ n j)^2)
    (hpeak : ∀ n, Even n → ∃ j, |μ n j| = m n)
    (hseries : ∀ᶠ n : ℕ in atTop, Even n → 0 < s n ∧ s n ≤ Real.log n)
    (hlower : ∀ D cutoff : ℕ, ∃ n ≥ cutoff, Even n ∧
      (Real.log n)^D < Real.sqrt n * m n) (k cutoff : ℕ) :
    ∃ n ≥ cutoff, Even n ∧ ∃ x : ℝ, 1 - 1/(Real.log n)^(k+1) < x ∧
      IsZero (weights (deltaSq n (s n)) (μ n)) (x : ℍ[ℝ]) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨b,hb⟩ := eventually_atTop.mp (hseries.and (hlog.eventually_ge_atTop 4))
  obtain ⟨n,hn,he,hbig⟩ := hlower ((k+1)+3) (max (max cutoff b) 1)
  have hcut : cutoff ≤ n := (le_max_left cutoff b).trans ((le_max_left _ _).trans hn)
  have hbn : b ≤ n := (le_max_right cutoff b).trans ((le_max_left _ _).trans hn)
  have hnpos : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hn))
  obtain ⟨⟨hs,hsL⟩,hL⟩ := And.intro ((hb n hbn).1 he) (hb n hbn).2
  obtain ⟨j,hj⟩ := hpeak n he
  have hbase : 1 ≤ (Real.log n)^k := one_le_pow₀ (by linarith)
  have hB : 2 ≤ (Real.log n)^(k+1) := by
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hbase (show 0 ≤ Real.log n by linarith)]
  rw [pow_add, ← hj] at hbig
  exact ⟨n,hcut,he,spike_gives_real_zero hnpos hL hs hsL hB (hsum n he) hbig⟩

end
end GoldbachSpectral
