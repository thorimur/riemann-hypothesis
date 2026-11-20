import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjQuotientOfRationalUnitaryDeterminantMa
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_quotient_of_rationalUnitaryDeterminantMap : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsRationalUnitaryDeterminantMap H (e1T H) ∧ (letI := H.cmStar; ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k) := by
  first | exact @GlobalTheory.Mem.RatPts.rat_points | exact GlobalTheory.Mem.RatPts.rat_points | (intros; apply GlobalTheory.Mem.RatPts.rat_points <;> assumption)
