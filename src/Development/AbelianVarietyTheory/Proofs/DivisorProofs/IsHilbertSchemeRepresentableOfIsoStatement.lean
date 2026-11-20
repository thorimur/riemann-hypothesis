import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIso
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_iso : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z), eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  first | exact @GlobalTheory.HilbertSch.isHilbRep_transfer | exact GlobalTheory.HilbertSch.isHilbRep_transfer | (intros; apply GlobalTheory.HilbertSch.isHilbRep_transfer <;> assumption)
