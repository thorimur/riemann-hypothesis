import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSaturated
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_filtration_saturated : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0), (l : A.Acr0) * z ∈ A.Fil0 r → z ∈ A.Fil0 r := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated | exact GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated | (intros; apply GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated <;> assumption)
