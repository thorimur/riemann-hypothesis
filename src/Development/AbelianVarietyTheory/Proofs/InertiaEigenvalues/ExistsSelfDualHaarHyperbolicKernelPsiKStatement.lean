import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualHaarHyperbolicKernelPsiK
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_haar_hyperbolicKernelPsiK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ x : A.Kˣ, ∃ ν : Measure A.K, SelfDual ν (Hyp.kx A ψ x) := by
  first | exact @GlobalTheory.JR.Hyp.selfDual_kx_exists | exact GlobalTheory.JR.Hyp.selfDual_kx_exists | (intros; apply GlobalTheory.JR.Hyp.selfDual_kx_exists <;> assumption)
