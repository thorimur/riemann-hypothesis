import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLeIffNormEmbedding
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_le_iff_norm_embedding : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l), Continuous φ → ∀ a b : F, a ≤ᵥ b ↔ ‖φ a‖ ≤ ‖φ b‖ := by
  first | exact @GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le | exact GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le | (intros; apply GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le <;> assumption)
