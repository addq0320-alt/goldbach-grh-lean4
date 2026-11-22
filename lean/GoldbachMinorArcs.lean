import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Fourier and moment identities in GoldbachMinorArcs.pdf.
Lean 4.19.0 and mathlib v4.19.0.
Run: lake env lean --trust=0 -DwarningAsError=true GoldbachMinorArcs.lean

The finite transform has no normalizing factor. All moduli with a primitive
additive character are allowed, including composite moduli. The analytic GRH
input, circle integrals over the major arcs, and the remaining minor-arc
estimate are distinguished in the accompanying paper.
-/

noncomputable section
namespace GoldbachMinorArcs
open Finset MeasureTheory
open scoped BigOperators ComplexConjugate

section Transform
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- Positive-sign Fourier transform, without normalization. -/
def fourier (ψ : AddChar R ℂ) (f : R → ℂ) (a : R) : ℂ :=
  ∑ r : R, f r * ψ (a*r)

/-- Summing over the additive numerator recovers a single residue class. -/
theorem numerator_inversion (ψ : AddChar R ℂ) (primitive : ψ.IsPrimitive)
    (f : R → ℂ) (t : R) :
    ∑ a : R, fourier ψ f a * ψ (-(a*t)) = (Fintype.card R : ℂ) * f t := by
  calc
    _ = ∑ a : R, ∑ r : R, f r * ψ (a*(r-t)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [fourier, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = ∑ r : R, f r * (∑ a : R, ψ (a*(r-t))) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp only [AddChar.sum_mulShift _ primitive, sub_eq_zero, mul_ite, mul_zero]
      simp [mul_comm]

/-- Bilinear version of Parseval that keeps all phases until the sum over rows. -/
theorem parseval_pair (ψ : AddChar R ℂ) (primitive : ψ.IsPrimitive)
    (f g : R → ℂ) :
    (∑ a : R, fourier ψ f a * fourier ψ g (-a)) =
      (Fintype.card R : ℂ) * ∑ r : R, f r * g r := by
  calc
    _ = ∑ a : R, ∑ r : R, (fourier ψ f a * ψ (-(a*r))) * g r := by
      apply Finset.sum_congr rfl
      intro a _
      change fourier ψ f a * (∑ r : R, g r * ψ ((-a)*r)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [neg_mul]
      ring
    _ = ∑ r : R, (∑ a : R, fourier ψ f a * ψ (-(a*r))) * g r := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      simp_rw [numerator_inversion ψ primitive]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- Full additive-row mean-square cancellation; the result is real-valued. -/
theorem parseval_energy (ψ : AddChar R ℂ) (primitive : ψ.IsPrimitive) (f : R → ℂ) :
    (∑ a : R, ‖fourier ψ f a‖^2) = (Fintype.card R : ℝ) * ∑ r : R, ‖f r‖^2 := by
  have conjF (a : R) : fourier ψ (fun r => conj (f r)) (-a) = conj (fourier ψ f a) := by
    simp [fourier, map_sum, map_mul, neg_mul, AddChar.map_neg_eq_conj]
  have h := parseval_pair ψ primitive f (fun r => conj (f r))
  simp only [conjF, Complex.mul_conj'] at h
  exact_mod_cast h

/-- Removing non-unit numerators can only decrease the row energy. -/
theorem reduced_rows_bound (ψ : AddChar R ℂ) (primitive : ψ.IsPrimitive)
    (s : Finset R) (f : R → ℂ) :
    (∑ a ∈ s, ‖fourier ψ f a‖^2) ≤ (Fintype.card R : ℝ) * ∑ r : R, ‖f r‖^2 := by
  rw [← parseval_energy ψ primitive]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ => sq_nonneg _)

/-- Additive convolution with counting measure. -/
def convolution (f g : R → ℂ) (t : R) : ℂ := ∑ r : R, f r * g (t-r)

omit [DecidableEq R] in
theorem convolution_transform (ψ : AddChar R ℂ) (f g : R → ℂ) (a : R) :
    fourier ψ (convolution f g) a = fourier ψ f a * fourier ψ g a := by
  calc
    _ = ∑ t : R, ∑ r : R, f r*g (t-r)*ψ (a*t) := by simp [fourier, convolution, Finset.sum_mul]
    _ = ∑ r : R, ∑ t : R, f r*g (t-r)*ψ (a*t) := Finset.sum_comm
    _ = ∑ r : R, (f r*ψ (a*r))*fourier ψ g a := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        _ = ∑ x : R, f r*g ((x+r)-r)*ψ (a*(x+r)) :=
          (Equiv.sum_comp (Equiv.addRight r) (fun t => f r*g (t-r)*ψ (a*t))).symm
        _ = _ := by
          simp only [add_sub_cancel_right, mul_add, AddChar.map_add_eq_mul, fourier, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = _ := (Finset.sum_mul ..).symm

/-- A sixth Fourier moment is the squared norm of a threefold signed convolution. -/
theorem sixth_convolution (ψ : AddChar R ℂ) (primitive : ψ.IsPrimitive) (f : R → ℂ) :
    (∑ a : R, ‖fourier ψ f a‖^6) =
      (Fintype.card R : ℝ) * ∑ t : R, ‖convolution (convolution f f) f t‖^2 := by
  rw [← parseval_energy ψ primitive]
  apply Finset.sum_congr rfl
  intro a _
  simp only [convolution_transform, norm_mul]
  ring

omit [DecidableEq R] in
/-- A frequency window depends on the difference of the two collective phases. -/
theorem window_pair (ψ : AddChar R ℂ) (w f g : R → ℂ) :
    (∑ a : R, w a * fourier ψ f a * fourier ψ g (-a)) =
    ∑ r : R, ∑ t : R, f r*g t*fourier ψ w (r-t) := by
  calc
    _ = ∑ a : R, ∑ r : R, ∑ t : R, f r*g t*(w a*ψ (a*(r-t))) := by
      apply Finset.sum_congr rfl
      intro a _
      unfold fourier
      rw [Finset.mul_sum Finset.univ (fun r : R => f r * ψ (a*r)) (w a), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, neg_mul]
      ring
    _ = ∑ r : R, ∑ t : R, ∑ a : R, f r*g t*(w a*ψ (a*(r-t))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro t _
      simp only [fourier, Finset.mul_sum, mul_comm (r-t) _]

omit [DecidableEq R] in
/-- Exact signed windowed sixth moment. C is the sum over each triple;
the remaining kernel only sees the difference of the triple frequencies. -/
theorem windowed_sixth (ψ : AddChar R ℂ) (w f : R → ℂ) :
    let C := convolution (convolution f f) f
    (∑ a : R, w a * ((‖fourier ψ f a‖^6 : ℝ) : ℂ)) =
      ∑ r : R, ∑ t : R, C r * conj (C t) * fourier ψ w (r-t) := by
  dsimp only
  let C := convolution (convolution f f) f
  change _ = ∑ r : R, ∑ t : R, C r * conj (C t) * fourier ψ w (r-t)
  rw [← window_pair]
  apply Finset.sum_congr rfl
  intro a _
  have hc : fourier ψ (fun t => conj (C t)) (-a) = conj (fourier ψ C a) := by
    simp [fourier, neg_mul, AddChar.map_neg_eq_conj]
  rw [hc, mul_assoc, Complex.mul_conj']
  simp only [C, convolution_transform, norm_mul, Complex.ofReal_pow, Complex.ofReal_mul]
  ring

/-- Complete Kloosterman sum, with both parameters allowed to vanish. -/
def kloosterman (ψ : AddChar R ℂ) (k b : R) : ℂ :=
  ∑ d : Rˣ, ψ (k*(d:R) + b*((d⁻¹:Rˣ):R))

/-- Finite completion of an arbitrary weight in the reciprocal variable.
The identity records exactly the factor later estimated with Weil's bound. -/
theorem complete_reciprocal (ψ : AddChar R ℂ) (primitive : ψ.IsPrimitive)
    (w : R → ℂ) (b : R) :
    (∑ a : R, fourier ψ w a * kloosterman ψ (-a) b) =
      (Fintype.card R : ℂ) * ∑ d : Rˣ, w d * ψ (b*((d⁻¹:Rˣ):R)) := by
  calc
    _ = ∑ a : R, ∑ d : Rˣ,
        (fourier ψ w a * ψ (-(a*(d:R)))) * ψ (b*((d⁻¹:Rˣ):R)) := by
      apply Finset.sum_congr rfl
      intro a _
      simp [kloosterman, Finset.mul_sum, AddChar.map_add_eq_mul, neg_mul, mul_assoc]
    _ = ∑ d : Rˣ, (∑ a : R, fourier ψ w a * ψ (-(a*(d:R)))) * ψ (b*((d⁻¹:Rˣ):R)) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      simp_rw [numerator_inversion ψ primitive]
      simp [Finset.mul_sum, mul_assoc]

omit [Fintype R] [DecidableEq R] in
/-- The congruence left by Poisson summation produces the reciprocal phase. -/
theorem poisson_phase (a h n l : R) (d : Rˣ) (hh : h = -(a*(d:R))) :
    a*(l-n) = (n-l)*h*((d⁻¹:Rˣ):R) := by
  subst h
  calc
    _ = (n-l)*(-(a*(d:R)))*((d⁻¹:Rˣ):R) := by
      have hc : (d:R)*((d⁻¹:Rˣ):R) = 1 := by simp
      linear_combination a*(n-l)*hc

/-- At the doubly zero parameter the complete sum has its full trivial size. -/
theorem degenerate_kloosterman (ψ : AddChar R ℂ) :
    kloosterman ψ 0 0 = (Fintype.card Rˣ : ℂ) := by simp [kloosterman]

end Transform

/-- Split after subtracting the common main term, keeping both linear errors. -/
theorem centered_product (a b u v : ℂ) :
    (a+u)*(b+v)-a*b = a*v+b*u+u*v := by ring

/-- Interpolation of a uniform coefficient bound with the summed square bound. -/
theorem sixth_interpolation {ι : Type*} (s : Finset ι) (f : ι → ℂ) {A B : ℝ}
    (hA : 0 ≤ A) (hu : ∀ i ∈ s, ‖f i‖ ≤ A) (h₂ : ∑ i ∈ s, ‖f i‖^2 ≤ B) :
    (∑ i ∈ s, ‖f i‖^6) ≤ A^4 * B := by
  calc
    _ ≤ ∑ i ∈ s, A^4 * ‖f i‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = ‖f i‖^4 * ‖f i‖^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hu i hi) 4)
          (sq_nonneg _)
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h₂ (pow_nonneg hA _)

/-- Off-resonant part of a complex integral controlled by its kernel cap. -/
theorem off_resonance_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F K : Ω → ℂ) {b : ℝ} (hF : Integrable (fun x => ‖F x‖) μ)
    (hK : ∀ x, ‖K x‖ ≤ b) :
    ‖∫ x, F x*K x ∂μ‖ ≤ b * ∫ x, ‖F x‖ ∂μ := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hF.const_mul _)
  exact Filter.Eventually.of_forall fun x => by
    rw [norm_mul, mul_comm b]
    exact mul_le_mul_of_nonneg_left (hK x) (norm_nonneg _)

/-- Pair correlation bound used at fixed differences or reflected differences.
For translated copies on a circle the two square integrals have the same cap. -/
theorem paired_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf₂ : Integrable (fun x => (f x)^2) μ) (hg₂ : Integrable (fun x => (g x)^2) μ)
    {E : ℝ} (h₁ : (∫ x, (f x)^2 ∂μ) ≤ E) (h₂ : (∫ x, (g x)^2 ∂μ) ≤ E) :
    (∫ x, |f x| * |g x| ∂μ) ≤ E := by
  have hmaj : Integrable (fun x => (1/2 : ℝ)*((f x)^2+(g x)^2)) μ := (hf₂.add hg₂).const_mul _
  have hdom (x : Ω) : |f x| * |g x| ≤ (1/2 : ℝ)*((f x)^2+(g x)^2) := by
    have hp := sq_nonneg (|f x|-|g x|)
    nlinarith only [hp, sq_abs (f x), sq_abs (g x)]
  have hi : Integrable (fun x => |f x| * |g x|) μ :=
    hmaj.mono' (hf.norm.mul hg.norm) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact hdom x)
  calc
    _ ≤ ∫ x, (1/2 : ℝ)*((f x)^2+(g x)^2) ∂μ := integral_mono hi hmaj hdom
    _ ≤ _ := by rw [integral_const_mul, integral_add hf₂ hg₂]; linarith

section Translations
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A translated pair has correlation bounded by the energy at zero shift. -/
theorem translate_pair (H : G → ℝ) (d : G) :
    (∑ x : G, H x * H (x+d)) ≤ ∑ x : G, (H x)^2 := by
  have he : (∑ x : G, (H (x+d))^2) = ∑ x : G, (H x)^2 :=
    Equiv.sum_comp (Equiv.addRight d) (fun x => (H x)^2)
  have hp (x : G) : 2*(H x*H (x+d)) ≤ (H x)^2+(H (x+d))^2 := by
    nlinarith only [sq_nonneg (H x-H (x+d))]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset G)) (fun x _ => hp x)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, he] at h
  linarith

/-- Summing over both remaining vertices costs the mass of the Poisson kernel,
even when the other frequencies have already shifted its center. -/
theorem closing_pair (H K : G → ℝ) (r : G) (hK : ∀ x, 0 ≤ K x) :
    (∑ x : G, ∑ y : G, H x*H y*K ((y-x)+r)) ≤
        (∑ a : G, K a)*(∑ x : G, (H x)^2) := by
  calc
    _ = ∑ x : G, ∑ d : G, H x*H (d+x)*K (d+r) := by
      apply Finset.sum_congr rfl
      intro x _
      have he := (Equiv.sum_comp (Equiv.addRight x) (fun y => H x*H y*K ((y-x)+r))).symm
      change (∑ y : G, H x*H y*K ((y-x)+r)) =
        ∑ d : G, H x*H (d+x)*K (((d+x)-x)+r) at he
      simpa only [add_sub_cancel_right] using he
    _ = ∑ d : G, (∑ x : G, H x*H (x+d))*K (d+r) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      simp only [Finset.sum_mul, add_comm d]
    _ ≤ ∑ d : G, (∑ x : G, (H x)^2)*K (d+r) :=
      Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (translate_pair H d) (hK _)
    _ = _ := by
      have he : (∑ d : G, K (d+r)) = ∑ d : G, K d := Equiv.sum_comp (Equiv.addRight r) K
      rw [← Finset.mul_sum, he, mul_comm]

/-- A third copy in an overlapping pair is bounded by one uniform cap. -/
theorem triple_cluster (H : G → ℝ) (b c : G) {A : ℝ}
    (nonneg : ∀ x, 0 ≤ H x) (cap : ∀ x, H x ≤ A) (hA : 0 ≤ A) :
    (∑ x : G, H x * H (x+b) * H (x+c)) ≤ A * ∑ x : G, (H x)^2 := by
  calc
    _ ≤ ∑ x : G, (H x * H (x+b))*A := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (cap _) (mul_nonneg (nonneg _) (nonneg _))
    _ = (∑ x : G, H x*H (x+b))*A := (Finset.sum_mul ..).symm
    _ ≤ _ := by rw [mul_comm A]; exact mul_le_mul_of_nonneg_right (translate_pair H b) hA

end Translations

/-- A coefficient can align perfectly with a phase even when an arbitrary
measurable set (for example all major arcs) has been removed. -/
theorem aligned_coefficient {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) (hs : MeasurableSet s) (χ : Ω → ℂ) (A : ℂ)
    (hχ : ∀ x, ‖χ x‖ = 1) :
    (∫ x, s.indicator (fun y => A * χ y) x * conj (χ x) ∂μ) = μ.real s • A := by
  have he (x : Ω) : s.indicator (fun y => A * χ y) x * conj (χ x) =
      s.indicator (fun _ => A) x := by
    by_cases hx : x ∈ s
    · simp [hx, mul_assoc, Complex.mul_conj', hχ]
    · simp [hx]
  simp_rw [he]
  exact integral_indicator_const A hs

/-- Write X=t². Both geometries of two distinct microscopic edges cost
exactly X^(11/2) L^12 when the input caps are saturated. -/
theorem two_edge_scales (t L : ℝ) (ht : 0 < t) :
    (t^5*L^4)^3/t^4 = t^11*L^12 ∧
    (t^3*L^3)*(t^2*L)*(t^5*L^4)^2/t^4 = t^11*L^12 := by
  constructor <;> field_simp <;> ring

/-- The three exponents are respectively the singular tail, linear part
and quadratic part of the normalized major-arc sixth moment. -/
def exponentBudget (θ δ : ℚ) : ℚ × ℚ × ℚ := (1-6*θ, -2+4*θ+5*δ, -5+12*θ+18*δ)

theorem logarithmic_width_exponents : exponentBudget (3/10) 0 = (-4/5, -4/5, -7/5) := by
  norm_num [exponentBudget]

theorem polynomial_width_exponents : exponentBudget (4/15) (1/15) = (-3/5, -3/5, -3/5) := by
  norm_num [exponentBudget]

/-- A widening inversely proportional to the denominator has the three
exponents on the right. Here θ=8/29 and γ=7/29. -/
theorem variable_width_exponents :
    let θ : ℚ := 8/29
    let γ : ℚ := 7/29
    (1-6*θ, -2+4*max θ γ+γ, -5+6*max (2*θ) (3*γ)) =
      ((-19/29 : ℚ), (-19/29 : ℚ), (-19/29 : ℚ)) := by
  norm_num

end GoldbachMinorArcs

open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``GoldbachMinorArcs.numerator_inversion, ``GoldbachMinorArcs.parseval_pair,
    ``GoldbachMinorArcs.parseval_energy, ``GoldbachMinorArcs.reduced_rows_bound,
    ``GoldbachMinorArcs.convolution_transform, ``GoldbachMinorArcs.sixth_convolution,
    ``GoldbachMinorArcs.window_pair, ``GoldbachMinorArcs.windowed_sixth,
    ``GoldbachMinorArcs.complete_reciprocal, ``GoldbachMinorArcs.poisson_phase, ``GoldbachMinorArcs.degenerate_kloosterman,
    ``GoldbachMinorArcs.centered_product, ``GoldbachMinorArcs.sixth_interpolation,
    ``GoldbachMinorArcs.off_resonance_integral, ``GoldbachMinorArcs.paired_integral,
    ``GoldbachMinorArcs.translate_pair, ``GoldbachMinorArcs.closing_pair,
    ``GoldbachMinorArcs.triple_cluster, ``GoldbachMinorArcs.aligned_coefficient,
    ``GoldbachMinorArcs.two_edge_scales, ``GoldbachMinorArcs.logarithmic_width_exponents,
    ``GoldbachMinorArcs.polynomial_width_exponents, ``GoldbachMinorArcs.variable_width_exponents]
  for n in names do
    let deps ← Lean.collectAxioms n
    unless deps.all allowed.contains do
      throwError "Unexpected axiom in {n}: {deps}"
    logInfo m!"{n}: {deps.qsort Name.lt |>.toList}"
