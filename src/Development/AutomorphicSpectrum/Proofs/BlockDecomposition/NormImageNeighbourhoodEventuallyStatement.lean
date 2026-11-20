import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormImageNeighbourhoodEventually
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_image_neighbourhood_eventually : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (t₀ : Eˣ) (T : Set Eˣ), T ∈ 𝓝 t₀ → ∀ᶠ a in 𝓝 (Algebra.norm F (t₀ : E)), ∃ t ∈ T, Algebra.norm F (t : E) = a := by
  first | exact @GlobalTheory.CompanionTheory.NormLocal.eventually_exists_norm_eq | exact GlobalTheory.CompanionTheory.NormLocal.eventually_exists_norm_eq | (intros; apply GlobalTheory.CompanionTheory.NormLocal.eventually_exists_norm_eq <;> assumption)
