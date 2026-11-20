import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorPointSemiFibration
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interior_point_semi_fibration : Hypotheses2 → HypothesesH → OnObj fun D O _ _ H _ => ∀ y : Pt O.s, y ∈ H.int → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (F : SemiFib K) (ι : K →+* Qb), F.P₀.g = D.R.f * O.N ∧ FibTie O y F ι := by
  first | exact @GlobalTheory.LieRead.fibAt_interior | exact GlobalTheory.LieRead.fibAt_interior | (intros; apply GlobalTheory.LieRead.fibAt_interior <;> assumption)
