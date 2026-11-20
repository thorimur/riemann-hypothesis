import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSectionContinuous
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_section_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω →
    ∀ (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f →
    ∀ (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)), IsCovolOne (ratL B A) ν 𝓖 →
    Continuous (swSection A B ν 𝓖 ω f) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous | exact GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous | (intros; apply GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous <;> assumption)
