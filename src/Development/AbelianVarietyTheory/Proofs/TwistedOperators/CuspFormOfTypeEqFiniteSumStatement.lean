import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormOfTypeEqFiniteSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_of_type_eq_finite_sum : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D), IsInfFam θ → N.V.SigOK → N.V.IsDefinite →
    ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
      ∃ (n : ℕ) (F : Fin n → N.Cusp θ) (w : Fin n → SmT N.M), φ = ∑ i, (F i).1 (w i) := by
  first | exact @GlobalTheory.DefiniteDecomp.cusp_decomp | exact GlobalTheory.DefiniteDecomp.cusp_decomp | (intros; apply GlobalTheory.DefiniteDecomp.cusp_decomp <;> assumption)
