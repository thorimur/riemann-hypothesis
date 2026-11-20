import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasurability
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_measurability : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (Φ : E → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ → ∃ R : ℝ, ∀ (κ : F) (ξ : E), gaussI χ μ Φ κ ξ ≠ 0 → (modulus ξ : ℝ) ≤ R * max 1 ((modulus κ : ℝ) ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.WcB.GaussSupport.gauss_support | exact GlobalTheory.CompanionTheory.WcB.GaussSupport.gauss_support | (intros; apply GlobalTheory.CompanionTheory.WcB.GaussSupport.gauss_support <;> assumption)
