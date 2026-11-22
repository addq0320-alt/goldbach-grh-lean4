import GoldbachResearch
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command
run_cmd do
  let modules := #["GoldbachDefect", "GoldbachDuality", "GoldbachFarey", "GoldbachFiveModuli", "GoldbachFreeLabels", "GoldbachMellin", "GoldbachMinorArcs", "GoldbachSeparationSieve", "GoldbachSpectral", "GoldbachThreeRoutes", "GoldbachWindows", "GoldbachZeroCorrelations"]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut checked := 0
  for (n, c) in env.constants.toList do
    if c.isTheorem && modules.contains n.getRoot.toString then
      let ax ← Lean.collectAxioms n
      unless ax.all allowed.contains do throwError "Unexpected axiom in {n}: {ax}"
      checked := checked+1
      logInfo m!"checked {n}"
  unless checked > 0 do throwError "No theorems found"
  logInfo m!"Verified axiom dependencies of {checked} named theorems."
