import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSchwartzParabolicEquivariant
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_schwartz_parabolic_equivariant : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (V : HSp D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)),
    IsWeilSch ψ χ θ V μ ω → ∀ (Φ : schwartzA θ V.rank n),
    ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      (ω (p * g) Φ).1 0 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) * (ω g Φ).1 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilLaw.weil_parabolic_law | exact GlobalTheory.CompanionTheory.WeilLaw.weil_parabolic_law | (intros; apply GlobalTheory.CompanionTheory.WeilLaw.weil_parabolic_law <;> assumption)
