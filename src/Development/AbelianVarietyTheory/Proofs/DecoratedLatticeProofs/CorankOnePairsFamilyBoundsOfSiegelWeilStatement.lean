import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOnePairsFamilyBoundsOfSiegelWeil
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corankOnePairsFamilyBounds_of_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false := by
  first | exact @GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil | exact GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil | (intros; apply GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil <;> assumption)
