import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOffSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_eq_one_off_splitPlace : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (κ : GA D V), Formalism.L2.Theta.SuppAt q.e V κ → Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 := by
  first | exact @GlobalTheory.SplitOffRed.redFn_eq_one_off | exact GlobalTheory.SplitOffRed.redFn_eq_one_off | (intros; apply GlobalTheory.SplitOffRed.redFn_eq_one_off <;> assumption)
