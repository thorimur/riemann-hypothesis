import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFiniteness
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_preserves_K_finiteness : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → ∀ (τ τ' : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ') → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ') e → GlobalTheory.CuspKFin.KFinAt θ N τ ψ → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ' (N.M.ε τ') (N.M.fr τ') e ψ) := by
  first | exact @GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt | exact GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt | (intros; apply GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt <;> assumption)
