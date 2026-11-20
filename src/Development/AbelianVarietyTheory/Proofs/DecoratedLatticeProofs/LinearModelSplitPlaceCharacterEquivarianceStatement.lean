import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivariance
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearModel_splitPlace_characterEquivariance : ∀ D : D7, GlobalTheory.FinPl.LinExact D := by
  first | exact @GlobalTheory.LinExactAt.linExact | exact GlobalTheory.LinExactAt.linExact | (intros; apply GlobalTheory.LinExactAt.linExact <;> assumption)
