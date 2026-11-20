import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalFlipOnVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_flip_on_volumes : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  first | exact @GlobalTheory.FlipRun.cuspStep_big | exact GlobalTheory.FlipRun.cuspStep_big | (intros; apply GlobalTheory.FlipRun.cuspStep_big <;> assumption)
