import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MajorantExistsAndWittDecomposition
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_exists_and_witt_decomposition : ∀ (D : D7) (W : HSp D), HSpace.SigOK W → (∃ b : GL (Fin W.rank) (AE D), IsMaj W b) ∧ (IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r') := by
  first | exact @GlobalTheory.Core.Rk.WittDec.maj_and_witt | exact GlobalTheory.Core.Rk.WittDec.maj_and_witt | (intros; apply GlobalTheory.Core.Rk.WittDec.maj_and_witt <;> assumption)
