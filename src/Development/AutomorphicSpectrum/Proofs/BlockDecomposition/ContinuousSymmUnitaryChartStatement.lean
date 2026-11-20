import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSymmUnitaryChart
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_symm_unitary_chart : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ (κ : GA D (dblSp A) ≃* G D A.rank), IsChart A μ κ →
    Continuous κ.symm := by
  first | exact @GlobalTheory.CompanionTheory.ChartSymm.continuous_symm | exact GlobalTheory.CompanionTheory.ChartSymm.continuous_symm | (intros; apply GlobalTheory.CompanionTheory.ChartSymm.continuous_symm <;> assumption)
