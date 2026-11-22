import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Finite inequalities for the separated-zeta-zero sum.
The Fourier sampling estimates and the use of GRH are in the companion paper. -/
noncomputable section
open Finset
open scoped BigOperators Classical
namespace GoldbachSeparationSieve

variable {I : Type*} [Fintype I]

/-- Inside a height cell the masses include zero multiplicities. -/
theorem weighted_cell_cs (m a : I → ℝ) (hm : ∀ i, 0 ≤ m i) :
    (∑ i, m i * |a i|)^2 ≤ (∑ i, m i) * ∑ i, m i * (a i)^2 := by
  have e (i : I) : Real.sqrt (m i) * (Real.sqrt (m i) * |a i|) = m i * |a i| := by
    rw [← mul_assoc, Real.mul_self_sqrt (hm i)]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (univ : Finset I)
    (fun i => Real.sqrt (m i)) (fun i => Real.sqrt (m i) * |a i|)
  simpa only [e, mul_pow, Real.sq_sqrt (hm _), sq_abs] using h

/-- A relation may be directed. Its row and column sums both matter. -/
theorem incidence_schur (K : I → I → ℝ) (u : I → ℝ) (D : ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (rows : ∀ i, (∑ j, K i j) ≤ D)
    (cols : ∀ j, (∑ i, K i j) ≤ D) :
    (∑ i, ∑ j, K i j * (u i * u j)) ≤ D * ∑ i, (u i)^2 := by
  have row : (∑ i, ∑ j, K i j * (u i)^2) ≤ D * ∑ i, (u i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (rows i) (sq_nonneg _)
  have col : (∑ i, ∑ j, K i j * (u j)^2) ≤ D * ∑ i, (u i)^2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (cols j) (sq_nonneg _)
  have h : (∑ i, ∑ j, 2 * (K i j * (u i * u j))) ≤
      ∑ i, ∑ j, (K i j * (u i)^2 + K i j * (u j)^2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    nlinarith [mul_nonneg (hK i j) (sq_nonneg (u i-u j))]
  simp_rw [← Finset.mul_sum] at h
  simp_rw [Finset.sum_add_distrib] at h
  linarith

/-- The squared norm of the three positive slots factorizes. -/
theorem triple_tensor_energy (u : I → ℝ) :
    (∑ i, ∑ j, ∑ k, (u i * u j * u k)^2) = (∑ i, (u i)^2)^3 := by
  calc
    _ = ∑ i, (u i)^2 * (∑ j, (u j)^2 * (∑ k, (u k)^2)) := by
      simp only [Finset.mul_sum, mul_pow, mul_assoc]
    _ = _ := by
      simp only [← Finset.sum_mul]
      ring

/-- Five differences and the bin sum fix the sixth difference. -/
theorem radial_fiber (a b : Fin 6 → ℤ)
    (hfirst : ∀ j : Fin 5, a j.castSucc = b j.castSucc)
    (hs : ∑ i, a i = ∑ i, b i) : a = b := by
  have hpart : (∑ j : Fin 5, a j.castSucc) = ∑ j : Fin 5, b j.castSucc :=
    Finset.sum_congr rfl (fun j _ => hfirst j)
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (f := b)] at hs
  funext i
  exact Fin.lastCases (by omega) (fun j => hfirst j) i

/-- The last coordinate can take at most one value for a fixed sum and prefix. -/
theorem radial_encoding_injective :
    Function.Injective (fun a : Fin 6 → ℤ => ((fun j : Fin 5 => a j.castSucc), ∑ i, a i)) := by
  intro a b h
  apply radial_fiber
  · intro j
    exact congrFun (congrArg Prod.fst h) j
  · exact congrArg Prod.snd h

/-- Six touched-slot costs, starting with the first possible pair. -/
def mixedError (a u : ℝ) : ℝ :=
  u^2*a^4 + u^3*a^3 + u^4*a^2 + u^5*a + u^6

theorem error_above (a u : ℝ) (hu : 0 ≤ u) (hua : u ≤ a) :
    mixedError a u ≤ 5 * u^2*a^4 := by
  have ha : 0 ≤ a := hu.trans hua
  have h : 0 ≤ u^2*(a-u)*(4*a^3 + 3*a^2*u + 2*a*u^2 + u^3) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hua)) (by positivity)
  unfold mixedError
  linarith only [show 0 ≤ 5*u^2*a^4 -
      (u^2*a^4 + u^3*a^3 + u^4*a^2 + u^5*a + u^6) by convert h using 1; ring]

theorem error_below (a u : ℝ) (ha : 0 ≤ a) (hau : a ≤ u) :
    mixedError a u ≤ 5*u^6 := by
  have hu : 0 ≤ u := ha.trans hau
  have h : 0 ≤ u^2*(u-a)*(4*u^3 + 3*u^2*a + 2*u*a^2 + a^3) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hau)) (by positivity)
  unfold mixedError
  linarith only [show 0 ≤ 5*u^6 -
      (u^2*a^4 + u^3*a^3 + u^4*a^2 + u^5*a + u^6) by convert h using 1; ring]

theorem positive_spike (a d u K : ℝ) (hu : 0 ≤ u) (hua : u ≤ a) (hK : 0 ≤ K)
    (herr : |d-a^6| ≤ K * mixedError a u) (hgap : 10*K*u^2 ≤ a^2) :
    a^6/2 ≤ d := by
  have h := (neg_abs_le (d-a^6)).trans' (neg_le_neg herr)
  have e := mul_le_mul_of_nonneg_left (error_above a u hu hua) hK
  have g := mul_le_mul_of_nonneg_right hgap (by positivity : 0 ≤ a^4)
  nlinarith only [h, e, g]

/-- Here X=t^10 and the side lengths of five difference windows are t^3. -/
theorem five_window_budget (t L : ℝ) :
    (t^3)^5 * (t^10)^4 * L^12 = t^55 * L^12 := by ring

/-- Here X=t^4 and the coarse height-bin length is t. -/
theorem coarse_bin_budget (t L : ℝ) :
    t^4 * ((t^2)*t*L^2)^6 = t^22 * L^12 := by ring

/-- Clip at twice the physical upper bound before summing the sixth moment. -/
theorem clip_sixth (c m e : ℝ) (hc : 0 ≤ c)
    (h : c ≤ m+e) : c^6 ≤ (2*m)^4*c^2 + (2*e)^6 := by
  by_cases hsmall : c ≤ 2*m
  · have hp := pow_le_pow_left₀ hc hsmall 4
    have hz := mul_le_mul_of_nonneg_right hp (sq_nonneg c)
    nlinarith only [hz, show 0 ≤ (2*e)^6 by positivity]
  · have hbig : c ≤ 2*e := by linarith
    have hp := pow_le_pow_left₀ hc hbig 6
    linarith only [hp, show 0 ≤ (2*m)^4*c^2 by positivity]

/-- The bin count may be certified directly as a cardinality via the encoding. -/
theorem finite_radial_count (s : Finset (Fin 6 → ℤ))
    (ranges : Finset (Fin 5 → ℤ)) (sums : Finset ℤ)
    (hp : ∀ a ∈ s, (fun i : Fin 5 => a i.castSucc) ∈ ranges)
    (hs : ∀ a ∈ s, (∑ i, a i) ∈ sums) :
    s.card ≤ ranges.card*sums.card := by
  classical
  let enc := fun a : Fin 6 → ℤ => ((fun j : Fin 5 => a j.castSucc), ∑ i, a i)
  have hsub : s.image enc ⊆ ranges ×ˢ sums := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
    exact Finset.mem_product.mpr ⟨hp a ha, hs a ha⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ radial_encoding_injective, Finset.card_product] at hle
  exact hle

/-- For an occupied complement, mean zero removes the zero Fourier frequency. -/
theorem forbidden_moments (p o : ℝ) (hp : 0 < p) (ho : 0 < o) :
    ((p-o) + o*(1-p/o))/p = 0 ∧
    ((p-o) + o*(1-p/o)^2)/p = (p-o)/o := by
  constructor <;> field_simp
  all_goals ring

/-- The complex coefficient test used at each squarefree modulus. -/
theorem sieve_test_bound (t w : I → ℂ) :
    ‖∑ i, t i*w i‖^2 ≤ (∑ i, ‖t i‖^2) * ∑ i, ‖w i‖^2 := by
  have h := norm_sum_le (univ : Finset I) (fun i => t i*w i)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) univ _ _)

/-- At least half of the Euler-product mass remains below the truncation. -/
theorem retained_mass (lo hi cost cap : ℝ) (hc : 0 < cap)
    (loss : cap*hi ≤ cost) (budget : 2*cost ≤ cap*(lo+hi)) :
    (lo+hi)/2 ≤ lo := by
  have h : cap*hi ≤ cap*lo := by linarith only [loss, budget]
  linarith only [le_of_mul_le_mul_left h hc]

/-- Combine a positive sieve denominator with the large-sieve inequality. -/
theorem sifted_card_budget (a d c : ℝ) (ha : 0 ≤ a) (hd : 0 < d) (hc : 0 ≤ c)
    (h : a^2*d ≤ c*a) : a ≤ c/d := by
  by_cases hz : a=0
  · simpa [hz] using (div_nonneg hc hd.le)
  · apply (le_div_iff₀ hd).2
    have hm : a*(a*d) ≤ a*c := by nlinarith only [h]
    exact le_of_mul_le_mul_left hm (lt_of_le_of_ne ha (Ne.symm hz))

/-- A point mass in the dual output sees the diagonal of the Gram matrix. -/
theorem gram_point_mass [DecidableEq I] (G : I → I → ℂ) (i : I) :
    (∑ j, ∑ k, (if j=i then (if k=i then G j k else 0) else 0)) = G i i := by
  classical
  simp

/-- The first difference window is balanced for the lower part of a dyadic block. -/
theorem lower_balanced_window (x n m : ℝ) (hn : x ≤ n) (hn' : n ≤ 3*x/2)
    (hm : x/2 ≤ m) (hm' : m ≤ 2*x/3) :
    n/3 ≤ m ∧ m ≤ 2*n/3 ∧ n/3 ≤ n-m ∧ n-m ≤ 2*n/3 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The second difference window is balanced for the upper part. -/
theorem upper_balanced_window (x n m : ℝ) (hn : 3*x/2 ≤ n) (hn' : n ≤ 2*x)
    (hm : 2*x/3 ≤ m) (hm' : m ≤ 5*x/6) :
    n/3 ≤ m ∧ m ≤ 2*n/3 ∧ n/3 ≤ n-m ∧ n-m ≤ 2*n/3 := by
  have hx : 0 ≤ x := by linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem balanced_window_width (x : ℝ) :
    2*x/3 - x/2 = x/6 ∧ 5*x/6 - 2*x/3 = x/6 := by
  constructor <;> ring

omit [Fintype I] in
/-- Charge each exceptional integer to a tested endpoint without losing its weight. -/
theorem weighted_witness_count {J : Type*} [Fintype J] (s : Finset I)
    (w : I → ℝ) (energy : J → I → ℝ) (he : ∀ j i, 0 ≤ energy j i)
    (hw : ∀ i ∈ s, ∃ j, w i ≤ energy j i) :
    (∑ i ∈ s, w i) ≤ ∑ j, ∑ i ∈ s, energy j i := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨j, hj⟩ := hw i hi
  exact hj.trans (Finset.single_le_sum (fun k _ => he k i) (Finset.mem_univ j))

end GoldbachSeparationSieve
open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``GoldbachSeparationSieve.weighted_cell_cs,
      ``GoldbachSeparationSieve.incidence_schur, ``GoldbachSeparationSieve.triple_tensor_energy,
      ``GoldbachSeparationSieve.radial_fiber, ``GoldbachSeparationSieve.radial_encoding_injective,
      ``GoldbachSeparationSieve.error_above, ``GoldbachSeparationSieve.error_below,
      ``GoldbachSeparationSieve.positive_spike, ``GoldbachSeparationSieve.five_window_budget,
      ``GoldbachSeparationSieve.coarse_bin_budget, ``GoldbachSeparationSieve.clip_sixth,
      ``GoldbachSeparationSieve.finite_radial_count, ``GoldbachSeparationSieve.forbidden_moments,
      ``GoldbachSeparationSieve.sieve_test_bound, ``GoldbachSeparationSieve.retained_mass,
      ``GoldbachSeparationSieve.sifted_card_budget, ``GoldbachSeparationSieve.gram_point_mass,
      ``GoldbachSeparationSieve.lower_balanced_window, ``GoldbachSeparationSieve.upper_balanced_window,
      ``GoldbachSeparationSieve.balanced_window_width, ``GoldbachSeparationSieve.weighted_witness_count] do
    let ax ← Lean.collectAxioms n
    unless ax.all allowed.contains do throwError "Unexpected axiom in {n}: {ax}"
    logInfo m!"{n}: {ax.qsort Name.lt |>.toList}"
