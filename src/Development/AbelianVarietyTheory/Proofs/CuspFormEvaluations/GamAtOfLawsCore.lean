import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruenceStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsCore : ∀ (D : D7) (T : Core D), LawsCore T → GamAt T := by
  intro D T h j hj σ hσ k γ h1 h2
  exact GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence D T h j hj σ hσ k γ h1 h2

end GlobalTheory.RunIn
