import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdParabolicTwistedTraceSumNeZeroOfVector
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdParabolicTwistedTraceSum_ne_zero_of_vector : ∀ (p : ℕ) [Fact p.Prime] (r a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (v : ρ), v ≠ 0 → StdVec ρ.ρ a θ v → stdTrace a θ ρ.character ≠ 0 := by
  first | exact @GlobalTheory.LevelType.stdTrace_ne_zero | exact GlobalTheory.LevelType.stdTrace_ne_zero | (intros; apply GlobalTheory.LevelType.stdTrace_ne_zero <;> assumption)
