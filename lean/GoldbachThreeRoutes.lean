import Mathlib.Algebra.Polynomial.Roots
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Finite claims in the paper on mixed characters, four moduli and cubic moments.
Run with Lean and mathlib v4.19.0. The analytic GRH input is used in the paper. -/
noncomputable section
namespace GoldbachThreeRoutes
open Finset
open scoped BigOperators Classical

section Algebra
variable {K : Type*} [Field K]

/-- Complete translated correlation of a nontrivial multiplicative character,
in ratio notation (the zero value at the pole is retained). -/
theorem character_ratio [Fintype K] [DecidableEq K] (χ : MulChar K ℂ)
    (hχ : χ ≠ 1) (d : K) :
    (∑ x : K, χ (x/(x-d))) = if d=0 then (Fintype.card K:ℂ)-1 else -1 := by
  by_cases hd : d=0
  · subst d
    simp only [sub_zero, if_pos rfl]
    have he (x : K) : χ (x/x) = 1-(if x=0 then 1 else 0) := by
      by_cases hx : x=0 <;> simp [hx, χ.map_zero]
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    simp
  · rw [if_neg hd]
    let e := ((Equiv.addRight (-d)).trans (Equiv.divLeft₀ d hd)).trans (Equiv.addRight 1)
    have hp : (∑ x : K, χ (d/(x-d)+1)) = 0 := by
      calc
        _ = ∑ x : K, χ x :=
          Fintype.sum_equiv e _ _ (fun x => by simp [e, sub_eq_add_neg])
        _ = _ := MulChar.sum_eq_zero_of_ne_one hχ
    have he (x : K) : χ (x/(x-d)) = χ (d/(x-d)+1) - (if x=d then 1 else 0) := by
      by_cases hx : x=d
      · subst x
        simp [χ.map_zero]
      · rw [if_neg hx, sub_zero]
        congr 1
        field_simp [sub_ne_zero.mpr hx]
    simp_rw [he]
    rw [Finset.sum_sub_distrib, hp]
    simp

/-- Orthogonality in both parameters of a translated multiplicative character. -/
theorem pair_rigidity (a b c d z : K) (hs : a+b=c+d)
    (hp : (a-z)*(b-z)=(c-z)*(d-z)) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hp' : a*b=c*d := by
    calc
      a*b = (a-z)*(b-z)+z*(a+b)-z^2 := by ring
      _ = (c-z)*(d-z)+z*(c+d)-z^2 := by rw [hp, hs]
      _ = c*d := by ring
  have hz : (a-c)*(a-d)=0 := by
    calc
      _ = a^2-a*(c+d)+c*d := by ring
      _ = 0 := by rw [← hs, ← hp']; ring
  rcases mul_eq_zero.mp hz with h | h
  · have ha := sub_eq_zero.mp h
    exact Or.inl ⟨ha, add_left_cancel (ha ▸ hs)⟩
  · have ha := sub_eq_zero.mp h
    have hbc : b=c := by
      rw [ha, add_comm c d] at hs
      exact add_left_cancel hs
    exact Or.inr ⟨ha,hbc⟩

/-- Shifted rational phase in one local arithmetic correlation. -/
theorem reciprocal_difference (a r u : K) (hr : r ≠ 0) (hru : r-u ≠ 0) :
    a/r - a/(r-u) = -a*u/(r*(r-u)) := by field_simp; ring

open Polynomial

def triple (a b c : K) : Multiset K := a ::ₘ b ::ₘ c ::ₘ 0

private theorem cubic_product (a b c : K) :
    (triple a b c |>.map (fun x => (X : K[X])-C x)).prod =
       X^3 - C (a+b+c)*X^2 + C (a*b+b*c+c*a)*X - C (a*b*c) := by
  simp [triple, map_add, map_mul]
  ring

/-- The fibers of the first three power sums contain one unordered triple. -/
theorem cubic_fiber (a b c u v w : K) (h₂ : (2:K) ≠ 0) (h₃ : (3:K) ≠ 0)
    (h1 : a+b+c=u+v+w) (h2 : a^2+b^2+c^2=u^2+v^2+w^2)
    (h3 : a^3+b^3+c^3=u^3+v^3+w^3) : triple a b c=triple u v w := by
  have hpair : a*b+b*c+c*a=u*v+v*w+w*u := by
    apply mul_left_cancel₀ h₂
    calc
      _ = (a+b+c)^2-(a^2+b^2+c^2) := by ring
      _ = (u+v+w)^2-(u^2+v^2+w^2) := by rw [h1, h2]
      _ = _ := by ring
  have hprod : a*b*c=u*v*w := by
    apply mul_left_cancel₀ h₃
    calc
      _ = a^3+b^3+c^3-(a+b+c)^3+3*(a+b+c)*(a*b+b*c+c*a) := by ring
      _ = u^3+v^3+w^3-(u+v+w)^3+3*(u+v+w)*(u*v+v*w+w*u) := by rw [h1,hpair,h3]
      _ = _ := by ring
  have hp : (triple a b c |>.map (fun z => (X : K[X])-C z)).prod =
      (triple u v w |>.map (fun z => (X : K[X])-C z)).prod := by
    rw [cubic_product, cubic_product, h1, hpair, hprod]
  simpa only [Polynomial.roots_multiset_prod_X_sub_C] using congrArg Polynomial.roots hp

/-- Twice the discriminant of three centered coordinates. -/
theorem centered_discriminant (a b c : K) (hs : a+b+c=0) :
    2*((a-b)*(b-c)*(c-a))^2 =
      (a^2+b^2+c^2)^3-6*(a^3+b^3+c^3)^2 := by
  have hc : c=-(a+b) := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hs)
  rw [hc]
  ring

theorem cubic_sign (q r t : K) (h6 : (6:K) ≠ 0)
    (h : q^3-6*r^2=q^3-6*t^2) : r=t ∨ r=-t := by
  have h2 : r^2=t^2 := mul_left_cancel₀ h6 (sub_right_inj.mp h)
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
end Algebra

section Counting
variable {I : Type*} [Fintype I]
theorem reflected_weight (u v : I → ℝ) (e : Equiv.Perm I) :
    (∑ c, (u c*v (e c))^2)^2 ≤ (∑ c, (u c)^4)*(∑ c, (v c)^4) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) univ
    (fun c => (u c)^2) (fun c => (v (e c))^2)
  have he : (∑ c, (v (e c))^4)=∑ c, (v c)^4 :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  simpa only [mul_pow, ← pow_mul, he] using h

/-- A leaf with at most D neighbors. -/
theorem leaf_bound (s : Finset I) (u : I → ℝ) :
    (∑ i ∈ s, |u i|)^2 ≤ (s.card:ℝ)*∑ i, (u i)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) s
    (fun _ => (1:ℝ)) (fun i => |u i|)
  simp only [one_mul, one_pow, sq_abs, sum_const, nsmul_eq_mul, mul_one] at h
  exact h.trans <| mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => sq_nonneg (u i)))
    (Nat.cast_nonneg _)

/-- The final undirected edge after stripping the other vertices. -/
theorem symmetric_schur (K : I → I → ℝ) (u : I → ℝ) (D : ℝ)
    (hk : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j=K j i)
    (hd : ∀ i, (∑ j, K i j) ≤ D) :
    (∑ i, ∑ j, K i j*(u i*u j)) ≤ D*∑ i, (u i)^2 := by
  have swap : (∑ i, ∑ j, K i j * (u j)^2) = ∑ i, ∑ j, K i j * (u i)^2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hsym j i]))
  have bound : (∑ i, ∑ j, K i j*(u i)^2) ≤ D*∑ i,(u i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hd i) (sq_nonneg _)
  have h : (∑ i, ∑ j, 2*(K i j*(u i*u j))) ≤
      ∑ i, ∑ j, (K i j*(u i)^2 + K i j*(u j)^2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    nlinarith [mul_nonneg (hk i j) (sq_nonneg (u i-u j))]
  simp_rw [← Finset.mul_sum] at h
  simp_rw [Finset.sum_add_distrib] at h
  rw [swap] at h
  linarith

omit [Fintype I] in
theorem bounded_fibers {J : Type*} [Fintype J] [DecidableEq J] (s : Finset I)
    (fiber : I → J) (w : I → ℝ) (k : ℝ)
    (h : ∀ j, (((s.filter fun i => fiber i=j).card : ℕ) : ℝ) ≤ k) :
    (∑ j, (∑ i ∈ s with fiber i=j, w i)^2) ≤ k*∑ i ∈ s, (w i)^2 := by
  calc
    _ ≤ ∑ j, k*∑ i ∈ s with fiber i=j, (w i)^2 := by
      apply Finset.sum_le_sum
      intro j _
      let t := s.filter (fun i => fiber i=j)
      have cs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) t (fun _ => (1:ℝ)) w
      simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at cs
      exact cs.trans (mul_le_mul_of_nonneg_right (h j) (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_fiberwise]

omit [Fintype I] in
theorem grouped_period_bound {J : Type*} [Fintype J] [DecidableEq J]
    (s : Finset I) (residue : I → J) (k : J → ℝ) (w : I → ℝ) :
    (∑ i ∈ s, k (residue i)*w i)^2 ≤
      (∑ a, (k a)^2) * ∑ a, (∑ i ∈ s with residue i=a, w i)^2 := by
  have he : (∑ i ∈ s, k (residue i)*w i) =
      ∑ a, k a*(∑ i ∈ s with residue i=a, w i) := by
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_fiberwise s residue (fun i => k (residue i)*w i)]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [he]
  exact Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) univ _ _
end Counting

/-- Common root-power exponents at the separation radius; X=x⁴. -/
theorem separation_budget (x L : ℝ) :
    x^4*(x^3*L^2)^6=x^22*L^12 := by ring

/-- Large-moment branch of the absorption in (8), in sixth-root variables. -/
theorem absorb_large (x u A D : ℝ) (hu : 0 ≤ u) (hux : u ≤ x) (hA : 0 ≤ A)
    (hsmall : 10*A*u^2 ≤ x^2)
    (h : x^6 ≤ D+A*(u^2*x^4+u^3*x^3+u^4*x^2+u^5*x+u^6)) :
    x^6 ≤ 2*D := by
  have hx := hu.trans hux
  have hc : u^2*x^4+u^3*x^3+u^4*x^2+u^5*x+u^6 ≤ 5*(u^2*x^4) := by
    calc
      _ = u^2*(x^4+u*x^3+u^2*x^2+u^3*x+u^4) := by ring
      _ ≤ u^2*(x^4+x*x^3+x^2*x^2+x^3*x+x^4) := by gcongr
      _ = 5*(u^2*x^4) := by ring
  have hp := mul_le_mul_of_nonneg_left hc hA
  have hb := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ x^4 by positivity)
  nlinarith only [h,hp,hb]

private theorem log_remainder_deriv (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ => Real.log (1+t)-t+t^2/2) (x^2/(1+x)) x := by
  have hn : 1+x ≠ 0 := by linarith
  have hd := (((Real.hasDerivAt_log hn).comp x
    ((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x))).sub
    (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).div_const 2)
  convert hd using 1
  dsimp
  field_simp
  ring

/-- Scalar integral underlying the third regularized Fredholm determinant. -/
theorem log_remainder_integral (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in (0 : ℝ)..x, t^2/(1+t)) = Real.log (1+x)-x+x^2/2 := by
  have hc : ContinuousOn (fun t : ℝ => t^2/(1+t)) (Set.uIcc 0 x) := by
    rw [Set.uIcc_of_le hx]
    exact (continuous_id.pow 2).continuousOn.div (continuous_const.add continuous_id).continuousOn
      (fun t ht => by have := ht.1; dsimp; linarith)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Real.log (1+t)-t+t^2/2)
    (fun t ht => log_remainder_deriv t (by rw [Set.uIcc_of_le hx] at ht; exact ht.1))
    hc.intervalIntegrable
  simpa using h

/-- Resolvent trace controls the cubic trace once the effective spectrum is bounded. -/
theorem resolvent_cap (u C : ℝ) (hc : u^3/(1+u) ≤ C)
    (hl : 1 ≤ u) : u^2 ≤ 2*C := by
  have hd : 0 < 1+u := by linarith
  have h1 : u^2/2 ≤ u^3/(1+u) := by
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hl)]
  linarith

end GoldbachThreeRoutes

open Lean Elab Command
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``GoldbachThreeRoutes.character_ratio, ``GoldbachThreeRoutes.pair_rigidity,
      ``GoldbachThreeRoutes.reciprocal_difference,
      ``GoldbachThreeRoutes.cubic_fiber, ``GoldbachThreeRoutes.centered_discriminant,
      ``GoldbachThreeRoutes.cubic_sign, ``GoldbachThreeRoutes.reflected_weight,
      ``GoldbachThreeRoutes.leaf_bound, ``GoldbachThreeRoutes.symmetric_schur,
      ``GoldbachThreeRoutes.bounded_fibers, ``GoldbachThreeRoutes.grouped_period_bound,
      ``GoldbachThreeRoutes.separation_budget, ``GoldbachThreeRoutes.absorb_large,
      ``GoldbachThreeRoutes.log_remainder_integral, ``GoldbachThreeRoutes.resolvent_cap] do
    let ax ← Lean.collectAxioms n
    unless ax.all allowed.contains do throwError "Unexpected axiom in {n}: {ax}"
    logInfo m!"{n}: {ax.qsort Name.lt |>.toList}"
