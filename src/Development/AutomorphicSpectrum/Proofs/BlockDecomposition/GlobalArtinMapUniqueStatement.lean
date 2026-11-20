import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalArtinMapUnique
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_artin_map_unique : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → art = (PositivityTheory.FamInh.art0 E Ω)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map | exact GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map | (intros; apply GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map <;> assumption)
