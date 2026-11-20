import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixRankMapField
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_map_ringHom : ∀ {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K), (M.map φ).rank = M.rank := by
  first | exact @GlobalTheory.matrix_rank_map_field | exact GlobalTheory.matrix_rank_map_field | (intros; apply GlobalTheory.matrix_rank_map_field <;> assumption)
