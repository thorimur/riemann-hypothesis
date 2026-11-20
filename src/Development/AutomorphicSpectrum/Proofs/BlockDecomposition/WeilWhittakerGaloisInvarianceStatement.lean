import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisInvariance
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_galois_invariance : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E), σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ (Φ : E → ℂ) (g : GL (Fin 2) F), g.val 1 0 ≠ 0 → GL2LocalData.Wc χ σ μ lam c Φ g ≠ 0 → ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det ∧ ‖GL2LocalData.Wc χ σ μ lam c Φ g‖ = ‖lam‖ * (modulus (g.val).det : ℝ) ^ (1 / 2 : ℝ) * (modulus (g.val 1 0) : ℝ)⁻¹ * ‖gaussI χ μ Φ (g.val 1 1 / g.val 1 0) (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹)‖ := by
  first | exact @GlobalTheory.CompanionTheory.WcB.value_lower_ne | exact GlobalTheory.CompanionTheory.WcB.value_lower_ne | (intros; apply GlobalTheory.CompanionTheory.WcB.value_lower_ne <;> assumption)
