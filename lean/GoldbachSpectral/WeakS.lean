import GoldbachSpectral.Obstruction

/-!
# The weak window and a separation example

The sufficient gain is quantitative. A specific one-eigenvalue model proves that a
large-norm lower bound of every logarithmic order can coexist with the weak window
for `h(n) = log(log n)`. The model is not a Li–Liu arithmetic operator.
-/
namespace GoldbachSpectral

open Filter
noncomputable section

def width (n s h : ℝ) : ℝ := h^2 * (Real.log n)^3 / (n*s)

/-- A sufficient estimate for the prescribed weak width. Obtaining this input
for the actual arithmetic eigenvalues for all sufficiently large even `n` remains open. -/
theorem weak_of_gain {n s h : ℝ} (hn : 0 < n) (hlog : 0 < Real.log n)
    (hs : 0 < s) (hh : 0 < h) (hadm : width n s h ≤ 1/2)
    {μ : ℕ → ℝ} (hsum : Summable fun j => (μ j)^2)
    (hgain : ∀ j, |μ j| ≤ s/(2*h)) :
    ZeroFree (weights (deltaSq n s) μ) (width n s h) := by
  have hd : 0 < deltaSq n s := by unfold deltaSq; positivity
  have he : 0 < width n s h := by unfold width; positivity
  have hw (j : ℕ) : 0 ≤ weights (deltaSq n s) μ j := by unfold weights; positivity
  apply (zeroFree_iff (weights_summable hsum _) hw he hadm).mpr
  intro j
  have hj : |μ j| * (2*h) ≤ s := (le_div_iff₀ (by positivity)).mp (hgain j)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ |μ j| * (2*h)) hj 2
  have heq : weights (deltaSq n s) μ j * width n s h = (|μ j| * (2*h))^2/s^2 := by
    unfold weights deltaSq width
    rw [mul_pow, sq_abs]
    field_simp [hs.ne',hlog.ne',hn.ne']; ring
  have h1 : weights (deltaSq n s) μ j * width n s h ≤ 1 := by
    rw [heq, div_le_one (sq_pos_of_pos hs)]; exact hsq
  rw [← mul_assoc]
  exact le_trans (mul_le_of_le_one_right (mul_nonneg (hw j) he.le) (by linarith)) h1

/-- Spectrum of a rank-one diagonal model; all modes except the first vanish. -/
def modelEigen (n j : ℕ) : ℝ := if j = 0 then 1/Real.log n else 0

private theorem log_pow_bound (D : ℕ) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (Real.log n)^D ≤ c * (n:ℝ)^r := by
  have h := (isLittleO_log_rpow_rpow_atTop (D:ℝ) hr).bound hc
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually h, (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 0]
    with n hb hl
  change 0 ≤ Real.log n at hl
  change ‖(Real.log n)^(D:ℝ)‖ ≤ c * ‖(n:ℝ)^r‖ at hb
  rwa [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hl _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hb

/-- A simultaneous statement with the correct quantifiers. For every fixed exponent,
all sufficiently large natural moduli in this model satisfy both the weak S conclusion
and the large-norm inequality. There is no restriction here to a subsequence. -/
theorem model_weak_and_spikes (D : ℕ) : ∀ᶠ n : ℕ in atTop,
    let L := Real.log n
    let η := width n 1 (Real.log L)
    (0 < η ∧ η ≤ 1/4) ∧ ZeroFree (weights (deltaSq n 1) (modelEigen n)) η ∧
      L^D < Real.sqrt n * |modelEigen n 0| := by
  have hL : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hslow := Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ) < 1/2)
  filter_upwards [hL.eventually hslow, hL.eventually_ge_atTop 4,
    log_pow_bound 5 (show (0:ℝ)<1 by norm_num) (show (0:ℝ)<1/4 by norm_num),
    log_pow_bound (D+1) (show (0:ℝ)<1/2 by norm_num) (show (0:ℝ)<1/2 by norm_num),
    eventually_ge_atTop (1:ℕ)] with n hslow_n hL4 h5 hp hn
  let L := Real.log n
  let h := Real.log L
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hh : 0 < h := Real.log_pos (by dsimp [L]; linarith)
  have hnpos : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  change ‖h‖ ≤ 1/2 * ‖L‖ at hslow_n
  rw [Real.norm_of_nonneg hh.le, Real.norm_of_nonneg hLpos.le] at hslow_n
  have hhL : h ≤ L := by linarith
  have hwidth : width n 1 h ≤ 1/4 := by
    unfold width
    rw [mul_one, div_le_iff₀ hnpos]
    change h^2 * L^3 ≤ _
    calc
      h^2 * L^3 ≤ L^2 * L^3 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh.le hhL 2) (pow_nonneg hLpos.le _)
      _ = L^5 := by ring
      _ ≤ _ := by simpa [L] using h5
  have hpos : 0 < width n 1 h := by unfold width; change 0 < h^2 * L^3 / _; positivity
  have hsum : Summable fun j => (modelEigen n j)^2 := by
    apply summable_of_ne_finset_zero (s := {0})
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [modelEigen,hj]
  have hgain (j : ℕ) : |modelEigen n j| ≤ 1/(2*h) := by
    by_cases hj : j = 0
    · simp only [modelEigen,if_pos hj]
      change |1/L| ≤ 1/(2*h)
      rw [abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    · simp only [modelEigen,if_neg hj,abs_zero]; positivity
  refine ⟨⟨hpos,hwidth⟩, weak_of_gain hnpos hLpos zero_lt_one hh (by linarith) hsum hgain,?_⟩
  change L^D < Real.sqrt n * |modelEigen n 0|
  simp only [modelEigen, if_pos rfl]
  change L^D < Real.sqrt n * |1/L|
  rw [abs_of_pos (by positivity), mul_one_div, lt_div_iff₀ hLpos]
  rw [← Real.sqrt_eq_rpow, pow_succ] at hp
  have hsqrt := Real.sqrt_pos.mpr hnpos
  dsimp [L]; linarith

end
end GoldbachSpectral
