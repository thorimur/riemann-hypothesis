import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFramesMovedTermUnitriangularChange
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFrames_movedTerm_unitriangular_change : ∀ {D : D7} (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (f' : Fin (D.R.rS + 1) → Vp D p), MovesTo F0 F0' F F' ρ U U' → Ext p ρ g → Tri (D.s.atP p).Ep (scaled Z p (frame F')) f' → Tri (D.s.atP p).Ep (scaled Z p (frame F0)) (fun a => g (scaled Z p (frame F) a)) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F0')) (fun b => g (f' b)) := by
  first | exact @GlobalTheory.LocOver.triMove_main | exact GlobalTheory.LocOver.triMove_main | (intros; apply GlobalTheory.LocOver.triMove_main <;> assumption)
