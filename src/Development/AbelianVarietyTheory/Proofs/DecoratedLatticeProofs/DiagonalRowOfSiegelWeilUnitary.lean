import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowBoundFromWindowWidthThree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateTermsAndCollisionBoundsUniformWidthsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOnePairsFamilyBoundsOfSiegelWeilStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk

theorem rowDiag_of_siegelWeilUnitary
    (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) :
    GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  have hDeg := GlobalTheory.T.degenerateTerms_and_collisionBounds_uniform_widths
  have hOne := GlobalTheory.T.corankOnePairsFamilyBounds_of_siegelWeil hSW 3
  exact GlobalTheory.Core.Rk.diagonalRow_bound_from_windowWidthThree GlobalTheory.wuDecayOfGap (hDeg.1 3) (hDeg.2 3) hOne.1 hOne.2

end GlobalTheory.Core.Rk
