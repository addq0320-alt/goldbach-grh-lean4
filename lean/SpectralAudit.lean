import GoldbachSpectral
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Reject any transitive theorem dependency on axioms outside the ordinary
classical Lean foundations. Every public theorem in this project is listed. -/
open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``GoldbachSpectral.covariance_difference,
    ``GoldbachSpectral.covariance_sum_difference,
    ``GoldbachSpectral.interior_signed_kernel,
    ``GoldbachSpectral.short_signed_kernel,
    ``GoldbachSpectral.interior_double_sum,
    ``GoldbachSpectral.interior_beta_reflection,
    ``GoldbachSpectral.buchstab_gap_unbounded,
    ``GoldbachSpectral.same_side_sum_ne_nat,
    ``GoldbachSpectral.same_side_beta_zero,
    ``GoldbachSpectral.same_side_arithmetic_zero,
    ``GoldbachSpectral.finite_kernel_entry,
    ``GoldbachSpectral.norm_le_iff_finite_tests,
    ``GoldbachSpectral.weights_summable,
    ``GoldbachSpectral.norm_dictionary,
    ``GoldbachSpectral.log_square_refutes_R,
    ``GoldbachSpectral.spike_gives_real_zero,
    ``GoldbachSpectral.obstruction_arbitrarily_large,
    ``GoldbachSpectral.product_zero_iff,
    ``GoldbachSpectral.spectralQuaternion_zero_iff,
    ``GoldbachSpectral.factor_slice_zero_iff,
    ``GoldbachSpectral.quaternion_zero_iff,
    ``GoldbachSpectral.right_real_zero_of_weight,
    ``GoldbachSpectral.zeroFree_iff,
    ``GoldbachSpectral.product_symm,
    ``GoldbachSpectral.critical_or_real,
    ``GoldbachSpectral.critical_iff,
    ``GoldbachSpectral.weak_of_gain,
    ``GoldbachSpectral.model_weak_and_spikes]
  for name in names do
    let dependencies ← Lean.collectAxioms name
    let extra := dependencies.filter fun a => !allowed.contains a
    unless extra.isEmpty do
      throwError "{name} has unexpected axioms: {extra}"
    logInfo m!"{name}  {dependencies.qsort Name.lt |>.toList}"
  logInfo m!"Axiom audit passed for {names.size} public theorems."
