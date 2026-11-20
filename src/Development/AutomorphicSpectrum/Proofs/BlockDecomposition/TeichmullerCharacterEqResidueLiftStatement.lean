import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCharacterEqResidueLift
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_character_eq_residue_lift : ∀ {l : ℕ} [Fact l.Prime] (q : ℕ), 2 ≤ q → l ∣ q → ∀ (x : Tl l) (y : Om l),
    x ^ q = x → y ^ q = y → sh x = omC y → tch l x = rB l y := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.tch_eq_rB_of_sh_eq | exact GlobalTheory.CompanionTheory.LTPer.Tilt.tch_eq_rB_of_sh_eq | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.tch_eq_rB_of_sh_eq <;> assumption)
