import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionConjugateApproximation
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_conjugate_approximation : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 → ∀ V ∈ 𝓝 a,
    ∃ b ∈ V, ∃ y : (Q d β (AF F))ˣ, ∃ x : Q d β F, qn x = 1 ∧ ∃ h ∈ SuppAt d β {s},
      (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) = b * h := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.KeyApprox.keyapprox | exact GlobalTheory.CompanionTheory.PlaneSA.KeyApprox.keyapprox | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.KeyApprox.keyapprox <;> assumption)
