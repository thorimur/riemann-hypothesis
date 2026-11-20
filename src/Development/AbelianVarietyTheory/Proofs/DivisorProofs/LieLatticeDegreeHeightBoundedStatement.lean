import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDegreeHeightBounded
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_degree_height_bounded : Hypotheses2 → HypothesesH → OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ y : Pt O.s, y ∈ H.int → ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K)), FibTie O y F ι → F.IsHerm h → |deg h F.lieLat + omHt O O.met.hm y| ≤ C := by
  first | exact @GlobalTheory.LieRead.deg_lieLat_add_omHt_le | exact GlobalTheory.LieRead.deg_lieLat_add_omHt_le | (intros; apply GlobalTheory.LieRead.deg_lieLat_add_omHt_le <;> assumption)
