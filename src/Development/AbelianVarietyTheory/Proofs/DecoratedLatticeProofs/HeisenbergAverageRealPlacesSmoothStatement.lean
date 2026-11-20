import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergAverageRealPlacesSmooth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergAverage_realPlaces_smooth : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (φ : GlobalTheory.FockCompare.RW T A → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ (f : WO A T → ℂ), Continuous f → GlobalTheory.FockCompare.Sm (GlobalTheory.FockCompare.iotaW σ T A) (fun w => ∫ x, (φ x : ℂ) * heisO ψ A T (GlobalTheory.FockCompare.iotaW σ T A x) f w) := by
  first | exact @GlobalTheory.HeisAverage.sm_heisO_average | exact GlobalTheory.HeisAverage.sm_heisO_average | (intros; apply GlobalTheory.HeisAverage.sm_heisO_average <;> assumption)
