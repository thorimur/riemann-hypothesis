import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomology
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_unramified_outside_cohomology : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (maxUnramifiedOutside F Ω S).fixingSubgroup ≤ NS Ω S := by
  first | exact @GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS | exact GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS | (intros; apply GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS <;> assumption)
