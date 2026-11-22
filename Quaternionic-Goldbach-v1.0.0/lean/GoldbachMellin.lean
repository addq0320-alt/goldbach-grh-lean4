import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Algebra and norm estimates in GoldbachMellin.pdf. Lean 4.19.0,
mathlib v4.19.0. The analytic GRH/Perron input, the circle-method argument,
and stationary-phase estimates are given in the paper.
-/

noncomputable section
namespace GoldbachMellin
open Finset MeasureTheory
open scoped BigOperators

/-- Fourier inversion of the unit indicator before grouping frequencies by denominator. -/
theorem unit_projector {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hp : ψ.IsPrimitive) (n : R) :
    (∑ a : R, ∑ r : R, (if IsUnit r then (1:ℂ) else 0) * ψ (a*(r-n))) =
      (Fintype.card R : ℂ) * (if IsUnit n then 1 else 0) := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hp]
  rw [Finset.sum_eq_single n]
  · simp [mul_comm]
  · intro r _ hr
    simp [sub_ne_zero.mpr hr]
  · simp

/-- The local Euler factor of the sum over q dividing the Type I modulus. -/
theorem ramanujan_factor (p : ℝ) (hp : p ≠ 1) (divides : Prop) [Decidable divides] :
    1-(if divides then p-1 else -1)/(p-1) = if divides then 0 else p/(p-1) := by
  have hn : p-1 ≠ 0 := sub_ne_zero.mpr hp
  by_cases h : divides
  · simp [h, hn]
  · simp only [h, if_false]
    field_simp

/-- A vanishing reciprocal frequency has precisely the total mass of the row. -/
theorem split_reciprocal {R : Type*} [CommRing R] [Fintype Rˣ]
    (ψ : AddChar R ℂ) (b : Rˣ → ℂ) (m : ℂ) (t : R) :
    (∑ r : Rˣ, b r * ψ (t*((r⁻¹:Rˣ):R))) =
      m * (∑ r : Rˣ, ψ (t*((r⁻¹:Rˣ):R))) +
      ∑ r : Rˣ, (b r-m) * ψ (t*((r⁻¹:Rˣ):R)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem centered_reciprocal_zero {R : Type*} [CommRing R] [Fintype Rˣ]
    (ψ : AddChar R ℂ) (b : Rˣ → ℂ) (m : ℂ)
    (hm : ∑ r : Rˣ, b r = (Fintype.card Rˣ : ℂ)*m) :
    (∑ r : Rˣ, (b r-m) * ψ ((0:R)*((r⁻¹:Rˣ):R))) = 0 := by
  simp [Finset.sum_sub_distrib, hm]

/-- Vaughan's decomposition in a commutative convolution ring. 'ones' represents
the constant-one arithmetic function and the ring unit the convolution identity. -/
theorem vaughan_split {R : Type*} [CommRing R] (μ ones Λ μs Λs : R)
    (h : μ * ones = 1) :
    Λ = μs * (ones * Λ) - μs * Λs * ones +
      (Λ-Λs) * ((μ-μs)*ones) + Λs := by
  have e : (μ-μs)*ones = 1-μs*ones := by rw [sub_mul, h]
  rw [e]
  ring

/-- Away from the zeros, the first term contains the whole logarithmic derivative.
The remaining expression is polynomial in the values of L, L', and the cutoffs. -/
theorem typeII_log_derivative {K : Type*} [Field K] (l lp m p : K) (hl : l ≠ 0) :
    (-(lp/l)-p)*(1-l*m) = -(lp/l) + lp*m-p+p*l*m := by
  field_simp
  ring

theorem zero_multiplier {K : Type*} [Ring K] (m : K) : 1-(0:K)*m=1 := by simp

/-- Multiplication by the truncated Vaughan multiplier preserves the residue.
'h' is a uniformizer, and 'f' the logarithmic derivative with its sign. -/
theorem pole_coefficient {α : Type*} {l : Filter α} {h f p g m : α → ℂ}
    {c p₀ m₀ : ℂ} (hh : Filter.Tendsto h l (nhds 0))
    (hf : Filter.Tendsto (fun x => h x*f x) l (nhds c))
    (hp : Filter.Tendsto p l (nhds p₀)) (hg : Filter.Tendsto g l (nhds 0))
    (hm : Filter.Tendsto m l (nhds m₀)) :
    Filter.Tendsto (fun x => h x*((f x-p x)*(1-g x*m x))) l (nhds c) := by
  have h1 := hf.sub (hh.mul hp)
  have h2 := (tendsto_const_nhds (x := (1:ℂ)) (f := l)).sub (hg.mul hm)
  have total := h1.mul h2
  simp only [zero_mul, sub_zero, mul_one] at total
  convert total using 1
  funext x
  ring

/-- Interchange a finite sum of squared row bounds with the common Perron integral. -/
theorem common_integral_rows {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset ι) (v : ι → ℝ) (g : ι → Ω → ℝ) (A : ℝ)
    (hg : ∀ i ∈ s, Integrable (g i) μ)
    (he : ∀ i ∈ s, v i ^ 2 ≤ A * ∫ t, g i t ∂μ) :
    ∑ i ∈ s, v i ^ 2 ≤ A * ∫ t, ∑ i ∈ s, g i t ∂μ := by
  rw [integral_finset_sum _ hg, Finset.mul_sum]
  exact Finset.sum_le_sum he

/-- Weighted sixth-moment interpolation. The cap and the second moment may be
proved by unrelated estimates. -/
theorem sixth_of_cap_and_energy {ι : Type*} (s : Finset ι) (w f : ι → ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hc : ∀ i ∈ s, f i ≤ A) (hE : ∑ i ∈ s, w i * (f i)^2 ≤ B) :
    ∑ i ∈ s, w i * (f i)^6 ≤ A^4 * B := by
  calc
    _ ≤ ∑ i ∈ s, A^4*(w i*(f i)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = (f i)^4*(w i*(f i)^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hf i hi) (hc i hi) 4)
          (mul_nonneg (hw i hi) (sq_nonneg _))
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (pow_nonneg hA 4)

/-- A short interval with a possibly large major-arc remainder. -/
theorem short_window_split {c m r : ℝ} (hc : 0 ≤ c) (hm : 0 ≤ m) (hr : 0 ≤ r)
    (h : c ≤ m+r) : c^6 ≤ (2*m)^4*c^2 + (2*r)^6 := by
  by_cases hsmall : c ≤ 2*m
  · calc
      _ = c^4*c^2 := by ring
      _ ≤ (2*m)^4*c^2 := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hc hsmall 4) (sq_nonneg _)
      _ ≤ _ := le_add_of_nonneg_right (pow_nonneg (by linarith) 6)
  · have hh : c ≤ 2*r := by linarith
    calc
      _ ≤ (2*r)^6 := pow_le_pow_left₀ hc hh 6
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (pow_nonneg (by linarith) 4) (sq_nonneg _))

/-- x = sqrt X. Interpolating the character-row estimate saves exactly one factor D. -/
theorem typeI_exponents (A x D L : ℝ) :
    (A*x*D*L^3)^4 * (A^2*x^4*D*L^6) = A^6*x^8*D^5*L^18 := by ring

/-- The Vaughan logarithm has already been included in the power 24 on the left. -/
theorem typeI_budget {x D L : ℝ} (hL : 0 ≤ L)
    (hD : D^5*L^15 ≤ x^3) : x^8*D^5*L^24 ≤ x^11*L^9 := by
  calc
    _ = (x^8*L^9)*(D^5*L^15) := by ring
    _ ≤ (x^8*L^9)*x^3 := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

/-- Solve the two Mellin critical point equations with a common additive frequency. -/
theorem critical_coordinates {u v z t s k : ℝ}
    (hz : u+v=z) (hu : t = -k*u) (hv : s = -k*v) (h : t+s ≠ 0) :
    u=z*t/(t+s) ∧ v=z*s/(t+s) := by
  constructor
  · apply (eq_div_iff h).2
    rw [← hz, hu, hv]
    ring
  · apply (eq_div_iff h).2
    rw [← hz, hu, hv]
    ring

theorem critical_same_sign {u v t s k : ℝ} (hu : 0 < u) (hv : 0 < v) (hk : k ≠ 0)
    (ht : t = -k*u) (hs : s = -k*v) : 0 < t*s := by
  rw [ht, hs]
  have he : (-k*u)*(-k*v)=k^2*u*v := by ring
  rw [he]
  exact mul_pos (mul_pos (sq_pos_of_ne_zero hk) hu) hv

/-- The actual first derivative of the additive-Mellin phase. -/
theorem outer_phase_derivative (T K z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (fun x : ℝ => T*Real.log x-K*x) (T/z-K) z := by
  simpa [div_eq_mul_inv] using
    ((Real.hasDerivAt_log hz).const_mul T).sub ((hasDerivAt_id z).const_mul K)

theorem outer_phase_curvature (T K z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (fun x : ℝ => T/x-K) (-(T/z^2)) z := by
  simpa [div_eq_mul_inv] using ((hasDerivAt_inv hz).const_mul T).sub_const K

/-- The mixed additive-Mellin resonance from even Poisson summation. -/
theorem hybrid_resonance {T z K Θ h : ℝ} (hz : z ≠ 0) (hK : K ≠ 0) :
    T/z-K*(Θ-h/2)=0 ↔ Θ-h/2=T/(K*z) := by
  constructor
  · intro he
    apply (eq_div_iff (mul_ne_zero hK hz)).2
    have he' := (div_eq_iff hz).1 (sub_eq_zero.mp he)
    rw [he']
    ring
  · intro he
    have he' := (eq_div_iff (mul_ne_zero hK hz)).1 he
    apply sub_eq_zero.mpr
    apply (div_eq_iff hz).2
    rw [← he']
    ring

/-- With one unmatched label on each side, the number of double slots per
modulus is the same by parity, including when the two unused counts are zero. -/
theorem modulus_balance {p n u v : ℕ} (h : 2*p+v=2*n+u) (hu : u≤1) (hv : v≤1) :
    p=n := by omega

/-- Simultaneous multiplication of the reduced numerators is a permutation.
A nontrivial total character forces its contribution to vanish exactly. -/
theorem orbit_cancellation {ι : Type*} [Fintype ι] (e : ι ≃ ι) (f : ι → ℂ)
    (c : ℂ) (hc : c ≠ 1) (he : ∀ a, f (e a) = c * f a) : ∑ a, f a = 0 := by
  have h : c * ∑ a, f a = ∑ a, f a := by
    rw [Finset.mul_sum]
    simpa only [he] using e.sum_comp f
  have h0 : (c-1) * ∑ a, f a = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

/-- The additive numerator homomorphism has equal-sized fibres over its image. -/
theorem equal_grid_fibres {G H : Type*} [AddGroup G] [AddGroup H]
    (f : G →+ H) (hf : Function.Surjective f) (a b : H) :
    Nat.card (f ⁻¹' ({a}:Set H)) = Nat.card (f ⁻¹' ({b}:Set H)) :=
  Nat.card_congr (AddMonoidHom.fiberEquivOfSurjective hf a b)

def jointModulus (q : ℕ × ℕ × ℕ) : ℕ := q.1.lcm (q.2.1.lcm q.2.2)

/-- Every coordinate of a triple with common modulus K lies in K.divisors. -/
theorem lcm_fibre_bound (s : Finset (ℕ × ℕ × ℕ)) {K : ℕ} (hK : K ≠ 0) :
    (s.filter (fun q => jointModulus q = K)).card ≤ K.divisors.card^3 := by
  have incl : s.filter (fun q => jointModulus q = K) ⊆
      K.divisors ×ˢ (K.divisors ×ˢ K.divisors) := by
    rintro ⟨a,b,c⟩ h
    have eqK : a.lcm (b.lcm c) = K := (Finset.mem_filter.mp h).2
    have hab : b.lcm c ∣ K := eqK ▸ Nat.dvd_lcm_right a (b.lcm c)
    have ha : a ∣ K := eqK ▸ Nat.dvd_lcm_left a (b.lcm c)
    exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨ha,hK⟩,
      Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_lcm_left b c) hab,hK⟩,
        Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_lcm_right b c) hab,hK⟩⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card incl
    _ = _ := by simp [pow_succ, mul_assoc]

/-- Weighted lcm regrouping used for the K^{-1} part of the numerator count. -/
theorem sum_by_lcm (s : Finset (ℕ × ℕ × ℕ)) (t : Finset ℕ) (w : ℕ → ℝ)
    (hm : ∀ q ∈ s, jointModulus q ∈ t) (h0 : ∀ k ∈ t, k ≠ 0)
    (hw : ∀ k ∈ t, 0 ≤ w k) :
    ∑ q ∈ s, w (jointModulus q) ≤ ∑ k ∈ t, (k.divisors.card:ℝ)^3*w k := by
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ = ∑ _q ∈ s.filter (fun q => jointModulus q=k), w k := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    _ = ((s.filter (fun q => jointModulus q=k)).card:ℝ)*w k := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (hw k hk)
      exact_mod_cast lcm_fibre_bound s (h0 k hk)

end GoldbachMellin

open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``GoldbachMellin.unit_projector, ``GoldbachMellin.ramanujan_factor,
    ``GoldbachMellin.split_reciprocal,
    ``GoldbachMellin.centered_reciprocal_zero, ``GoldbachMellin.vaughan_split,
    ``GoldbachMellin.typeII_log_derivative, ``GoldbachMellin.zero_multiplier,
    ``GoldbachMellin.pole_coefficient,
    ``GoldbachMellin.common_integral_rows, ``GoldbachMellin.sixth_of_cap_and_energy,
    ``GoldbachMellin.short_window_split, ``GoldbachMellin.typeI_exponents,
    ``GoldbachMellin.typeI_budget, ``GoldbachMellin.critical_coordinates,
    ``GoldbachMellin.critical_same_sign, ``GoldbachMellin.outer_phase_derivative,
    ``GoldbachMellin.outer_phase_curvature, ``GoldbachMellin.hybrid_resonance,
    ``GoldbachMellin.modulus_balance, ``GoldbachMellin.orbit_cancellation,
    ``GoldbachMellin.equal_grid_fibres,
    ``GoldbachMellin.lcm_fibre_bound, ``GoldbachMellin.sum_by_lcm]
  for n in names do
    let deps ← Lean.collectAxioms n
    unless deps.all allowed.contains do
      throwError "Unexpected axiom in {n}: {deps}"
    logInfo m!"{n}  {deps.qsort Name.lt |>.toList}"
