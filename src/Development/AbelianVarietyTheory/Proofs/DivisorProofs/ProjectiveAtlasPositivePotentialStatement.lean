import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveAtlasPositivePotential
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_atlas_positive_potential : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (B : FinHolAtlas n Y), IsProjective B → ∃ Om : LocPot Y, IsPotential B Om ∧ IsPosPot B Om := by
  first | exact @GlobalTheory.FubiniStudyPot.exists_posPot | exact GlobalTheory.FubiniStudyPot.exists_posPot | (intros; apply GlobalTheory.FubiniStudyPot.exists_posPot <;> assumption)
