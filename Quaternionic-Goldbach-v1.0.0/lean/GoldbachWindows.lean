import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Parts of the proof in GoldbachWindows.pdf. Lean 4.19.0, mathlib v4.19.0.
Run: lake env lean --trust=0 -DwarningAsError=true GoldbachWindows.lean
The Selberg integral and the Hardy-space identification are analytic inputs
in the paper. The finite-field calculation below has no analytic hypotheses.
-/

namespace GoldbachWindows

open Finset MeasureTheory
open scoped BigOperators Interval

/-- Sliding intervals overlap in a triangular weight. Endpoint conventions
have no effect on Lebesgue measure. -/
theorem tent_overlap (m p q h : ℝ) :
    volume.real (Set.Ioc (p-h) p ∩ Set.Ioc (m-q-h) (m-q)) =
      max (h-|p+q-m|) 0 := by
  rw [Set.Ioc_inter_Ioc, Real.volume_real_Ioc]
  change max (min p (m-q) - max (p-h) (m-q-h)) 0 = _
  congr 1
  by_cases hx : p ≤ m-q
  · rw [min_eq_left hx, max_eq_right (by linarith : p-h ≤ m-q-h),
      abs_of_nonpos (by linarith : p+q-m ≤ 0)]
    ring
  · rw [min_eq_right (le_of_not_ge hx), max_eq_left (by linarith : m-q-h ≤ p-h),
      abs_of_nonneg (by linarith : 0 ≤ p+q-m)]
    ring

/-- The linear error in a short prime interval only contributes two boundary
integrals after averaging its left endpoint. -/
theorem linear_boundary (f : ℝ → ℝ) (a b h : ℝ)
    (hi : ∀ c d : ℝ, IntervalIntegrable f volume c d) :
    (∫ x in a..b, (f (x+h)-f x)) =
      (∫ x in b..b+h, f x) - ∫ x in a..a+h, f x := by
  have hshift : IntervalIntegrable (fun x => f (x+h)) volume a b := by
    simpa using (hi (a+h) (b+h)).comp_add_right h
  rw [intervalIntegral.integral_sub hshift (hi a b), intervalIntegral.integral_comp_add_right]
  linarith only [intervalIntegral.integral_add_adjacent_intervals (hi a (a+h)) (hi (a+h) (b+h)),
    intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b (b+h))]

/-- The quadratic remainder of the product of the short-interval errors
is controlled by the two Selberg integrals. Integrability of the product
is a consequence of square integrability and measurability. -/
theorem integrated_cross_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf₂ : Integrable (fun x => (f x)^2) μ)
    (hg₂ : Integrable (fun x => (g x)^2) μ) :
    |∫ x, f x*g x ∂μ| ≤ (1/2 : ℝ)*((∫ x, (f x)^2 ∂μ)+(∫ x, (g x)^2 ∂μ)) := by
  have major : Integrable (fun x => (1/2 : ℝ)*((f x)^2+(g x)^2)) μ :=
    (hf₂.add hg₂).const_mul _
  have hp (x : Ω) : |f x*g x| ≤ (1/2 : ℝ)*((f x)^2+(g x)^2) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [sq_nonneg (f x+g x), sq_nonneg (f x-g x)]
  have hfg : Integrable (fun x => f x*g x) μ := major.mono' (hf.mul hg)
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hp x)
  calc
    _ ≤ ∫ x, |f x*g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (1/2 : ℝ)*((f x)^2+(g x)^2) ∂μ := integral_mono hfg.abs major hp
    _ = _ := by rw [integral_const_mul, integral_add hf₂ hg₂]

/-- On an interval with its measure normalized to mass one, the cube
of the mean square is bounded by the sixth moment, as in (7) for k=3. -/
theorem sixth_moment_transfer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf₂ : Integrable (fun x => (f x)^2) μ) (hf₆ : Integrable (fun x => (f x)^6) μ) :
    (∫ x, (f x)^2 ∂μ)^3 ≤ ∫ x, (f x)^6 ∂μ := by
  let m := ∫ x, (f x)^2 ∂μ
  have hm : 0 ≤ m := integral_nonneg fun x => sq_nonneg (f x)
  have hlin : Integrable (fun x => (3*m^2)*(f x)^2) μ := hf₂.const_mul _
  have hconst : Integrable (fun _ : Ω => 2*m^3) μ := integrable_const _
  have hbound (x : Ω) : (3*m^2)*(f x)^2 - 2*m^3 ≤ (f x)^6 := by
    have hn : 0 ≤ (f x)^2+2*m := by linarith only [sq_nonneg (f x), hm]
    nlinarith only [mul_nonneg (sq_nonneg ((f x)^2-m)) hn]
  have H := integral_mono (hlin.sub hconst) hf₆ hbound
  change (∫ x, (3*m^2)*(f x)^2-2*m^3 ∂μ) ≤ _ at H
  rw [integral_sub hlin hconst, integral_const_mul] at H
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at H
  change (3*m^2)*m-2*m^3 ≤ _ at H
  change m^3 ≤ _
  linarith only [H]

/-- A positive amount of weighted mass on a finite set forces many indices
if each weight is small and the weighted second moment is bounded. -/
theorem mass_cardinality {ι : Type*} (s : Finset ι) (w v : ι → ℝ) {cap : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hc : ∀ i ∈ s, w i ≤ cap) :
    (∑ i ∈ s, w i*v i)^2 ≤
      ((s.card : ℝ)*cap) * ∑ i ∈ s, w i*(v i)^2 := by
  have hcap : ∑ i ∈ s, w i ≤ (s.card : ℝ)*cap := by
    calc
      _ ≤ ∑ _i ∈ s, cap := Finset.sum_le_sum hc
      _ = _ := by simp
  have hsum : (∑ i ∈ s, w i*v i) =
      ∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i)*v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  rw [hsum]
  calc
    _ ≤ (∑ i ∈ s, (Real.sqrt (w i))^2) *
        ∑ i ∈ s, (Real.sqrt (w i)*v i)^2 := Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ = (∑ i ∈ s, w i) * ∑ i ∈ s, w i*(v i)^2 := by
      congr 1
      · exact Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hw i hi)
      · apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow, Real.sq_sqrt (hw i hi)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcap
      (Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))

/-- If a signed average is small, a large value forces variation from its
neighbors. The weights need not sum to one. -/
theorem variation_bound {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Finset ι) (w : ι → ℝ) (A : ι → V) (v : V) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i) * ‖v‖ ≤ ‖∑ i ∈ s, w i • A i‖ +
      ∑ i ∈ s, w i * ‖v-A i‖ := by
  have hn : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  have he : (∑ i ∈ s, w i) • v =
      (∑ i ∈ s, w i • A i) + ∑ i ∈ s, w i • (v-A i) := by
    rw [Finset.sum_smul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← smul_add]
    simp
  calc
    _ = ‖(∑ i ∈ s, w i) • v‖ := by rw [norm_smul, Real.norm_of_nonneg hn]
    _ ≤ ‖∑ i ∈ s, w i • A i‖ + ‖∑ i ∈ s, w i • (v-A i)‖ := he ▸ norm_add_le _ _
    _ ≤ _ := add_le_add_left (norm_sum_le_of_le _ (fun i hi => by
      rw [norm_smul, Real.norm_of_nonneg (hw i hi)])) _

/-- Unnormalized positive moments control every entry, including an isolated
exception. This is used with exponent six in the paper. -/
theorem pointwise_from_moment {ι : Type*} (s : Finset ι) (d : ι → ℝ)
    {i : ι} (hi : i ∈ s) (k : ℕ) {M : ℝ} (hm : ∑ j ∈ s, (d j)^(2*k) ≤ M) :
    (d i)^(2*k) ≤ M := by
  apply le_trans _ hm
  exact Finset.single_le_sum (f := fun j => (d j)^(2*k))
    (fun j _ => by
      change 0 ≤ (d j)^(2*k)
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _) hi

section FiniteField
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The affine line with the two forbidden residues removed counts the
local factors in the Goldbach singular series. -/
theorem local_fiber_card (t : F) :
    (Finset.univ.filter (fun x : F => x ≠ 0 ∧ t-x ≠ 0)).card =
      if t = 0 then Fintype.card F - 1 else Fintype.card F - 2 := by
  classical
  have he : Finset.univ.filter (fun x : F => x ≠ 0 ∧ t-x ≠ 0) =
      Finset.univ \ ({0,t} : Finset F) := by
    ext x
    simp [sub_ne_zero, ne_comm, and_comm]
  rw [he, Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ]
  by_cases ht : t = 0
  · simp [ht]
  · rw [if_neg ht, Finset.card_pair (Ne.symm ht)]

/-- An unnormalized reflected correlation for the genuine quadratic character. -/
def reflection (t : F) : ℤ := ∑ x : F, quadraticChar F x * quadraticChar F (t-x)

private theorem neg_one_value (hq : Fintype.card F % 4 = 3) :
    quadraticChar F (-1) = -1 := by
  apply quadraticChar_neg_one_iff_not_isSquare.mpr
  intro h
  exact (FiniteField.isSquare_neg_one_iff.mp h) hq

/-- The entire correlation function, for every finite field of cardinality
3 mod 4. Only the center zero is exceptional. -/
theorem reflection_exact (hq : Fintype.card F % 4 = 3) (t : F) :
    reflection t = if t = 0 then 1-(Fintype.card F : ℤ) else 1 := by
  have hn := neg_one_value hq
  by_cases ht : t = 0
  · subst t
    rw [if_pos rfl]
    calc
      _ = ∑ x : F, ((if x = 0 then (1 : ℤ) else 0)-1) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = 0
        · simp [hx]
        · rw [if_neg hx, zero_sub, ← neg_one_mul x, map_mul, hn]
          have hs := quadraticChar_sq_one hx
          nlinarith only [hs]
      _ = _ := by simp [Finset.sum_sub_distrib]
  · rw [if_neg ht]
    have hchar : ringChar F ≠ 2 := fun h =>
      (quadraticChar_neg_one_iff_not_isSquare.mp hn) (FiniteField.isSquare_of_char_two h _)
    calc
      _ = ∑ x : F, quadraticChar F (t*x) * quadraticChar F (t-t*x) :=
        (Equiv.sum_comp (Equiv.mulLeft₀ t ht)
          (fun x => quadraticChar F x * quadraticChar F (t-x))).symm
      _ = ∑ x : F, quadraticChar F x * quadraticChar F (1-x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [show t-t*x = t*(1-x) by ring, map_mul, map_mul]
        calc
          _ = quadraticChar F t ^ 2 * (quadraticChar F x * quadraticChar F (1-x)) := by ring
          _ = _ := by rw [quadraticChar_sq_one ht, one_mul]
      _ = -quadraticChar F (-1) := by
        change jacobiSum (quadraticChar F) (quadraticChar F) = _
        simpa only [(quadraticChar_isQuadratic F).inv] using
          jacobiSum_nontrivial_inv (quadraticChar_ne_one hchar)
      _ = 1 := by rw [hn]; decide

/-- Translated nonzero quadratic residues omit the prescribed sum a+a. -/
theorem prescribed_missing_sum (hq : Fintype.card F % 4 = 3) (a x y : F)
    (hx : quadraticChar F (x-a) = 1) (hy : quadraticChar F (y-a) = 1) :
    x+y ≠ a+a := by
  intro he
  have hop : y-a = (-1)*(x-a) := by linear_combination he
  rw [hop, map_mul, neg_one_value hq, hx] at hy
  norm_num at hy

/-- The Fourier phases of the translate align at a+a. The sum here is
unnormalized; for the conventional transform divide its square by q². -/
theorem translated_fourier_square (hq : Fintype.card F % 4 = 3) (a : F)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    (∑ x : F, (quadraticChar F (x-a) : ℂ)*ψ x)^2 =
      -(Fintype.card F : ℂ)*ψ (a+a) := by
  let φ : ℤ →+* ℂ := Int.castRingHom ℂ
  let χ : MulChar F ℂ := (quadraticChar F).ringHomComp φ
  have hn := neg_one_value hq
  have ho : ringChar F ≠ 2 := fun h =>
    (quadraticChar_neg_one_iff_not_isSquare.mp hn) (FiniteField.isSquare_of_char_two h _)
  have hi : Function.Injective φ := Int.cast_injective
  have hc : χ ≠ 1 := (MulChar.ringHomComp_ne_one_iff hi).mpr (quadraticChar_ne_one ho)
  have hGauss : (∑ x : F, (quadraticChar F x : ℂ)*ψ x)^2 = -(Fintype.card F : ℂ) := by
    have hg := gaussSum_sq hc ((quadraticChar_isQuadratic F).comp φ)
      (AddChar.IsPrimitive.of_ne_one hψ)
    simpa [gaussSum, χ, φ, MulChar.ringHomComp_apply, hn] using hg
  have he : (∑ x : F, (quadraticChar F (x-a) : ℂ)*ψ x) =
      (∑ x : F, (quadraticChar F x : ℂ)*ψ x)*ψ a := by
    calc
      _ = ∑ x : F, (quadraticChar F ((x+a)-a) : ℂ)*ψ (x+a) :=
        (Equiv.sum_comp (Equiv.addRight a) (fun x => (quadraticChar F (x-a) : ℂ)*ψ x)).symm
      _ = _ := by simp [Finset.sum_mul, AddChar.map_add_eq_mul, mul_assoc]
  rw [he, mul_pow, hGauss, AddChar.map_add_eq_mul, pow_two]

/-- All even moments have a single term accounting for the anomalous center. -/
theorem all_reflection_moments (hq : Fintype.card F % 4 = 3) (k : ℕ) :
    (∑ t : F, (reflection t)^(2*k)) =
      (1-(Fintype.card F : ℤ))^(2*k) + (Fintype.card F : ℤ)-1 := by
  let z : ℤ := (1-(Fintype.card F : ℤ))^(2*k)
  calc
    _ = ∑ t : F, ((if t = 0 then z-1 else 0)+1) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t = 0 <;> simp [reflection_exact hq, ht, z]
    _ = _ := by
      simp [Finset.sum_add_distrib, z]
      ring

end FiniteField
end GoldbachWindows

open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``GoldbachWindows.tent_overlap, ``GoldbachWindows.linear_boundary,
    ``GoldbachWindows.integrated_cross_error, ``GoldbachWindows.sixth_moment_transfer,
    ``GoldbachWindows.mass_cardinality,
    ``GoldbachWindows.variation_bound, ``GoldbachWindows.pointwise_from_moment,
    ``GoldbachWindows.local_fiber_card, ``GoldbachWindows.reflection_exact,
    ``GoldbachWindows.prescribed_missing_sum, ``GoldbachWindows.translated_fourier_square,
    ``GoldbachWindows.all_reflection_moments]
  for nm in names do
    let deps ← Lean.collectAxioms nm
    unless deps.all allowed.contains do
      throwError "Unexpected axiom in {nm}: {deps}"
    logInfo m!"{nm}  {deps.qsort Name.lt |>.toList}"
