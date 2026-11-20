import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealActionOnVertexWeightContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realActionOnVertexWeight_continuous : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D), IsInfFam θ →
    ∀ (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (Λ : Module.Dual ℂ (VV ℂ (wt G X))) (w : VV ℂ (wt G X)),
    Continuous fun k : GinfC (G.V X) => Λ (realAct θ fr X ((k : GA D (G.V X))⁻¹) w) := by
  first | exact @GlobalTheory.RealActCont.realAct_inv_continuous | exact GlobalTheory.RealActCont.realAct_inv_continuous | (intros; apply GlobalTheory.RealActCont.realAct_inv_continuous <;> assumption)
