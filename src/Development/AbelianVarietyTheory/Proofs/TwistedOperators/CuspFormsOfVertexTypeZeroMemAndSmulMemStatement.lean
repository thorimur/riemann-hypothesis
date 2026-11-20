import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormsOfVertexTypeZeroMemAndSmulMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)), (0 : GA D N.V → ℂ) ∈ Cls θ N U ∧ ∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U := by
  first | exact @GlobalTheory.PlaceDecomp.cls_zero_smul | exact GlobalTheory.PlaceDecomp.cls_zero_smul | (intros; apply GlobalTheory.PlaceDecomp.cls_zero_smul <;> assumption)
