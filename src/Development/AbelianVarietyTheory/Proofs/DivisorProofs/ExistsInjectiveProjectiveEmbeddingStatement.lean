import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveProjectiveEmbedding
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points GlobalTheory.CxPts
open scoped LinearAlgebra.Projectivization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_projective_embedding : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (N : ℕ) (i : X ⟶ PSpace k N) [IsClosedImmersion i], i ≫ PSpace.str k N = p → ∃ F : CxPts p σ → ℙ ℂ (Fin (N + 1) → ℂ), Function.Injective F ∧ ∀ (a : Fin (N + 1)) (y : CxPts p σ), y ∈ ptsIn p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) → ∃ h : (fun j => ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) y) ≠ 0, F y = Projectivization.mk ℂ _ h := by
  first | exact @GlobalTheory.complexPts_proj_rep | exact GlobalTheory.complexPts_proj_rep | (intros; apply GlobalTheory.complexPts_proj_rep <;> assumption)
