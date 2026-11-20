import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerCmLogPeriodEqConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory.LamT

theorem exists_kronecker_logOm_core : ∀ (D : D7) (T : Core D) (h : LawsCore T) (large₂ : SizeData₂ D), ∃ (_ : NeZero T.Q.H.d) (χ : DirichletCharacter ℂ T.Q.H.d), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm :=
  fun D T h large₂ => GlobalTheory.LamF.exists_kronecker_logOm_eq D T.Q h.pins.1 large₂

end GlobalTheory.LamT
