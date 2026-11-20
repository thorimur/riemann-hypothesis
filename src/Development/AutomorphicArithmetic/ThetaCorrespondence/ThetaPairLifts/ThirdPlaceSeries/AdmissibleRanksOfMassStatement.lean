import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksOfMass

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_frame_all_members' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) := by
  first | exact @_root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked_of_recT | exact _root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked_of_recT | (intros; apply _root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked_of_recT <;> assumption)
end
