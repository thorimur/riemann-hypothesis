import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisConvOfSteps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SwSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralNeTopOfBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TermInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerAbsOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspKillHolds

open Formalism.BasicNotions

namespace GlobalTheory.RawLift.Assembled

theorem rallisConv_of_siegelWeil : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary →
    ∀ D : D7, GlobalTheory.RawLift.RallisConv D :=
  fun hP hW D => GlobalTheory.RawLift.rallisConv_of_steps D (GlobalTheory.SWPairProof.swPair hW D) (GlobalTheory.EisAbsPf.eisAbs hP D)
    (GlobalTheory.RawLift.kerAbs_of_cuspRapidDecay hP D) (GlobalTheory.RawLift.Move.termMove D) (GlobalTheory.TermInvProof.termInv D)
    (GlobalTheory.CuspKillProof.cuspKill_holds D)

end GlobalTheory.RawLift.Assembled
