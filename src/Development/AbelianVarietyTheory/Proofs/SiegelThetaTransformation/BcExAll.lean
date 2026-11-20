import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.FramedBaseChange

theorem bcEx_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ σ : c.F →+* ℂ, BCEx Xo c σ :=
  fun E _ _ _ H Dw l Xo c σ p y ψ =>
    exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c p.R (CAt σ) ψ y

end GlobalTheory.FramedBaseChange
