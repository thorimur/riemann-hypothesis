import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfFilteredColimit
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_filtered_colimit : ∀ (q : ℕ) [NeZero q] (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ j, IsUnit (q : D.obj j)) → (∀ j, HInv q (D.obj j)) → HInv q c.pt := by
  first | (exact @GlobalTheory.EtC.hInv_of_filtered_colimit) | (exact GlobalTheory.EtC.hInv_of_filtered_colimit) | (intros; apply GlobalTheory.EtC.hInv_of_filtered_colimit  <;> assumption)
