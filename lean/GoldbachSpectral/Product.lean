import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Li–Liu spectral products on quaternionic slices

`w j` is the dimensionless coefficient `4 * μⱼ² / δ²`. The arithmetic
source of this sequence plays no role in this module. For any summable
nonnegative real sequence we characterize the zeros of the infinite
product, including equality at the boundary of the open half-space.
-/

namespace GoldbachSpectral

open scoped Quaternion
noncomputable section

def factor (w : ℝ) (z : ℂ) : ℂ := 1 - (w : ℂ) * (z * (1 - z))

def spectralProduct (w : ℕ → ℝ) (z : ℂ) : ℂ := ∏' j, factor (w j) z

/-- Summability excludes zeros caused solely by a vanishing limit of nonzero products. -/
theorem product_zero_iff {w : ℕ → ℝ} (hw : Summable w) (z : ℂ) :
    spectralProduct w z = 0 ↔ ∃ j, factor (w j) z = 0 := by
  constructor
  · intro h
    by_contra hnone
    have hn : ∀ j, factor (w j) z ≠ 0 := fun j hj => hnone ⟨j, hj⟩
    have hs : Summable (fun j => (w j : ℂ) * -(z * (1 - z))) :=
      (Complex.summable_ofReal.mpr hw).mul_right _
    have hl : Summable (fun j => Complex.log (factor (w j) z)) := by
      simpa [factor, sub_eq_add_neg, mul_neg] using Complex.summable_log_one_add_of_summable hs
    exact Complex.exp_ne_zero _ ((Complex.cexp_tsum_eq_tprod hn hl).trans h)
  · exact tprod_of_exists_eq_zero

/-- The complex representative in the upper half of a quaternion's slice. -/
def sliceParameter (q : ℍ[ℝ]) : ℂ :=
  ⟨q.re, Real.sqrt (q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2)⟩

/-- Zero locus of the intrinsic product, evaluated in the slice containing `q`. -/
def IsZero (w : ℕ → ℝ) (q : ℍ[ℝ]) : Prop := spectralProduct w (sliceParameter q) = 0

def quatFactor (w : ℝ) (q : ℍ[ℝ]) : ℍ[ℝ] := 1 - w • (q * (1 - q))

private theorem factor_re (w : ℝ) (z : ℂ) :
    (factor w z).re = 1 - w * (z.re * (1 - z.re) + z.im ^ 2) := by
  simp only [factor, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem factor_im (w : ℝ) (z : ℂ) :
    (factor w z).im = -(w * (1 - 2*z.re)) * z.im := by
  simp only [factor, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem slice_im_sq (q : ℍ[ℝ]) :
    (sliceParameter q).im ^ 2 = q.imI^2 + q.imJ^2 + q.imK^2 :=
  Real.sq_sqrt (by positivity)

private theorem slice_im_eq_zero_iff (q : ℍ[ℝ]) :
    (sliceParameter q).im = 0 ↔ q.imI = 0 ∧ q.imJ = 0 ∧ q.imK = 0 := by
  constructor
  · intro h
    have hs := slice_im_sq q
    rw [h, zero_pow (by decide : 2 ≠ 0)] at hs
    constructor
    · nlinarith [sq_nonneg q.imJ, sq_nonneg q.imK, sq_nonneg q.imI]
    constructor <;> nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
  · rintro ⟨hi,hj,hk⟩
    simp [sliceParameter,hi,hj,hk]

/-- Transport a complex value back to the oriented slice determined by `q`.
At a real argument we use the standard `i` slice. -/
def fromSlice (q : ℍ[ℝ]) (z : ℂ) : ℍ[ℝ] :=
  let y := (sliceParameter q).im
  if y = 0 then ⟨z.re,z.im,0,0⟩
  else ⟨z.re,(z.im/y)*q.imI,(z.im/y)*q.imJ,(z.im/y)*q.imK⟩

/-- The quaternion-valued function is defined by its convergent complex product on each slice. -/
def spectralQuaternion (w : ℕ → ℝ) (q : ℍ[ℝ]) : ℍ[ℝ] :=
  fromSlice q (spectralProduct w (sliceParameter q))

private theorem fromSlice_zero_iff (q : ℍ[ℝ]) (z : ℂ) : fromSlice q z = 0 ↔ z = 0 := by
  constructor
  · intro h
    by_cases hy : (sliceParameter q).im = 0
    · simp only [fromSlice,hy,if_pos] at h
      exact Complex.ext (congrArg QuaternionAlgebra.re h) (congrArg QuaternionAlgebra.imI h)
    · simp only [fromSlice,if_neg hy] at h
      apply Complex.ext (congrArg QuaternionAlgebra.re h)
      change z.im = 0
      by_contra him
      have hc := div_ne_zero him hy
      have i : z.im / (sliceParameter q).im * q.imI = 0 := congrArg QuaternionAlgebra.imI h
      have j : z.im / (sliceParameter q).im * q.imJ = 0 := congrArg QuaternionAlgebra.imJ h
      have k : z.im / (sliceParameter q).im * q.imK = 0 := congrArg QuaternionAlgebra.imK h
      exact hy ((slice_im_eq_zero_iff q).mpr ⟨(mul_eq_zero.mp i).resolve_left hc,
        (mul_eq_zero.mp j).resolve_left hc,(mul_eq_zero.mp k).resolve_left hc⟩)
  · rintro rfl
    simp [fromSlice]
    rfl

theorem spectralQuaternion_zero_iff (w : ℕ → ℝ) (q : ℍ[ℝ]) :
    spectralQuaternion w q = 0 ↔ IsZero w q := fromSlice_zero_iff _ _

/-- This connects the slice definition to multiplication of actual Hamilton quaternions. -/
theorem factor_slice_zero_iff (w : ℝ) (q : ℍ[ℝ]) :
    factor w (sliceParameter q) = 0 ↔ quatFactor w q = 0 := by
  let b : ℝ := -(w * (1 - 2*q.re))
  have hr : (quatFactor w q).re = (factor w (sliceParameter q)).re := by
    rw [factor_re, slice_im_sq]
    change _ = 1 - w * (q.re * (1 - q.re) + _)
    simp only [quatFactor, Quaternion.sub_re, Quaternion.one_re, Quaternion.smul_re,
      smul_eq_mul, Quaternion.mul_re, Quaternion.sub_imI, Quaternion.sub_imJ, Quaternion.sub_imK,
      Quaternion.one_imI, Quaternion.one_imJ, Quaternion.one_imK]
    ring
  have hi : (quatFactor w q).imI = b * q.imI := by simp [quatFactor,b]; ring
  have hj : (quatFactor w q).imJ = b * q.imJ := by simp [quatFactor,b]; ring
  have hk : (quatFactor w q).imK = b * q.imK := by simp [quatFactor,b]; ring
  have hc : (factor w (sliceParameter q)).im = b * (sliceParameter q).im := factor_im _ _
  constructor
  · intro h
    have hy : b * (sliceParameter q).im = 0 := by rw [← hc, h, Complex.zero_im]
    apply Quaternion.ext
    · rw [hr, h]; rfl
    · rw [hi, Quaternion.zero_imI]
      rcases mul_eq_zero.mp hy with hb | hb
      · simp [hb]
      · simp [((slice_im_eq_zero_iff q).mp hb).1]
    · rw [hj, Quaternion.zero_imJ]
      rcases mul_eq_zero.mp hy with hb | hb
      · simp [hb]
      · simp [((slice_im_eq_zero_iff q).mp hb).2.1]
    · rw [hk, Quaternion.zero_imK]
      rcases mul_eq_zero.mp hy with hb | hb
      · simp [hb]
      · simp [((slice_im_eq_zero_iff q).mp hb).2.2]
  · intro h
    apply Complex.ext
    · rw [← hr, h]; rfl
    · rw [hc, Complex.zero_im]
      by_cases hb : b = 0
      · simp [hb]
      · apply mul_eq_zero_of_right
        apply (slice_im_eq_zero_iff q).mpr
        exact ⟨(mul_eq_zero.mp (hi.symm.trans (by rw [h]; rfl))).resolve_left hb,
          (mul_eq_zero.mp (hj.symm.trans (by rw [h]; rfl))).resolve_left hb,
          (mul_eq_zero.mp (hk.symm.trans (by rw [h]; rfl))).resolve_left hb⟩

theorem quaternion_zero_iff {w : ℕ → ℝ} (hw : Summable w) (q : ℍ[ℝ]) :
    IsZero w q ↔ ∃ j, quatFactor (w j) q = 0 := by
  unfold IsZero
  rw [product_zero_iff hw]
  exact exists_congr fun j => factor_slice_zero_iff (w j) q

private theorem real_factor_zero_iff (w x : ℝ) :
    factor w (x : ℂ) = 0 ↔ w * (x * (1-x)) = 1 := by
  rw [Complex.ext_iff, factor_re, factor_im]
  simp
  constructor <;> intro h <;> linarith

private theorem real_slice (x : ℝ) : sliceParameter (x : ℍ[ℝ]) = (x : ℂ) := by
  apply Complex.ext <;> simp [sliceParameter]

/-- A real zero beyond the right boundary exists precisely above the threshold.
The converse uses IVT between `1-η` and `1`; strictness at the former is essential. -/
private theorem exists_right_real_zero {w η : ℝ} (hη : 0 < η) (hw : 1 < w * (η*(1-η))) :
    ∃ x : ℝ, 1-η < x ∧ factor w (x : ℂ) = 0 := by
  let f (x : ℝ) := w * (x*(1-x))
  have hleft : 1 < f (1-η) := by dsimp [f]; nlinarith
  have hright : f 1 = 0 := by simp [f]
  have hmem : (1:ℝ) ∈ Set.Icc (f 1) (f (1-η)) := ⟨by rw [hright]; norm_num, hleft.le⟩
  obtain ⟨x,hx,hfx⟩ := intermediate_value_Icc' (show 1-η ≤ 1 by linarith)
    (f := f) (by dsimp [f]; fun_prop) hmem
  refine ⟨x, lt_of_le_of_ne hx.1 ?_, (real_factor_zero_iff w x).2 hfx⟩
  intro heq
  rw [← heq] at hfx
  linarith

/-- A single oversized weight supplies a real quaternionic zero with larger real part. -/
theorem right_real_zero_of_weight {w : ℕ → ℝ} (hs : Summable w) {η : ℝ} (hη : 0 < η)
    {j : ℕ} (hj : 1 < w j * (η*(1-η))) :
    ∃ x : ℝ, 1-η < x ∧ IsZero w (x : ℍ[ℝ]) := by
  obtain ⟨x,hx,hf⟩ := exists_right_real_zero hη hj
  refine ⟨x,hx,?_⟩
  unfold IsZero
  rw [real_slice, product_zero_iff hs]
  exact ⟨j,hf⟩

def ZeroFree (w : ℕ → ℝ) (η : ℝ) : Prop :=
  ∀ q : ℍ[ℝ], IsZero w q → q.re ≤ 1-η

/-- The endpoint `η = 1/2` is included. Equality in the coefficient bound is allowed. -/
theorem zeroFree_iff {w : ℕ → ℝ} (hs : Summable w) (hw : ∀ j, 0 ≤ w j)
    {η : ℝ} (hη : 0 < η) (hhalf : η ≤ 1/2) :
    ZeroFree w η ↔ ∀ j, w j * (η*(1-η)) ≤ 1 := by
  constructor
  · intro hf j
    by_contra! h
    obtain ⟨x,hx,hzero⟩ := right_real_zero_of_weight hs hη h
    exact (not_le_of_gt hx) (hf _ hzero)
  · intro h q hz
    by_contra! hx
    obtain ⟨j,hj⟩ := (product_zero_iff hs (sliceParameter q)).mp hz
    have hr := congrArg Complex.re hj
    have hi := congrArg Complex.im hj
    rw [factor_re, Complex.zero_re] at hr
    rw [factor_im, Complex.zero_im] at hi
    change 1 - w j * (q.re*(1-q.re) + (sliceParameter q).im^2) = 0 at hr
    change -(w j * (1-2*q.re)) * (sliceParameter q).im = 0 at hi
    have hwpos : 0 < w j := lt_of_le_of_ne (hw j) (by rintro heq; rw [← heq] at hr; linarith)
    have hlin : 1-2*q.re ≠ 0 := by linarith
    have hy := (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr (mul_ne_zero hwpos.ne' hlin))
    rw [hy] at hr
    have hstrict : q.re*(1-q.re) < η*(1-η) := by
      nlinarith [mul_pos (show 0 < q.re-(1-η) by linarith) (show 0 < q.re-η by linarith)]
    linarith [mul_lt_mul_of_pos_left hstrict hwpos, h j]

/-- Symmetry of the complex product implies the left critical boundary as well. -/
theorem product_symm (w : ℕ → ℝ) (z : ℂ) : spectralProduct w (1-z) = spectralProduct w z := by
  unfold spectralProduct
  apply tprod_congr
  intro j
  simp [factor, mul_comm]

private theorem factor_zero_critical_or_real {w : ℝ} {z : ℂ} (h : factor w z = 0) :
    z.re = 1/2 ∨ z.im = 0 := by
  have hne : w ≠ 0 := by rintro rfl; simp [factor] at h
  have hi := congrArg Complex.im h
  rw [factor_im, Complex.zero_im] at hi
  rcases mul_eq_zero.mp hi with hleft | hright
  · left
    have hh := (mul_eq_zero.mp (neg_eq_zero.mp hleft)).resolve_left hne
    linarith
  · exact Or.inr hright

/-- Every quaternionic zero off the critical hyperplane is real. This applies without first restricting to one chosen complex subalgebra. -/
theorem critical_or_real {w : ℕ → ℝ} (hs : Summable w) {q : ℍ[ℝ]} (h : IsZero w q) :
    q.re = 1/2 ∨ q = (q.re : ℍ[ℝ]) := by
  obtain ⟨j,hj⟩ := (product_zero_iff hs (sliceParameter q)).mp h
  rcases factor_zero_critical_or_real hj with hx | hy
  · exact Or.inl hx
  · obtain ⟨hi,hj',hk⟩ := (slice_im_eq_zero_iff q).mp hy
    exact Or.inr (Quaternion.ext q _ rfl hi hj' hk)

/-- The strong critical-hyperplane hypothesis, including equality at weight four. -/
theorem critical_iff {w : ℕ → ℝ} (hs : Summable w) (hw : ∀ j, 0 ≤ w j) :
    (∀ q : ℍ[ℝ], IsZero w q → q.re = 1/2) ↔ ∀ j, w j ≤ 4 := by
  have hd := zeroFree_iff hs hw (η := 1/2) (by norm_num) le_rfl
  constructor
  · intro hc j
    have hz : ZeroFree w (1/2) := by
      intro q hq
      rw [hc q hq]
      norm_num
    have := hd.mp hz j
    linarith
  · intro h
    have hz : ZeroFree w (1/2) := hd.mpr (fun j => by linarith [h j])
    intro q hq
    rcases critical_or_real hs hq with he | hr
    · exact he
    · have hright := hz q hq
      have hp : spectralProduct w (q.re : ℂ) = 0 := by
        unfold IsZero at hq
        conv at hq => lhs; arg 2; rw [hr, real_slice]
        simpa using hq
      have hz' : IsZero w ((1 - q.re : ℝ) : ℍ[ℝ]) := by
        unfold IsZero
        rw [real_slice, Complex.ofReal_sub, Complex.ofReal_one, product_symm, hp]
      have hleft := hz _ hz'
      change 1-q.re ≤ 1-1/2 at hleft
      linarith

end
end GoldbachSpectral
