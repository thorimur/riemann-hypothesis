import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFromPadicUniqueOfSep
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_hom_from_padic_unique_of_sep : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [Ring R], (∀ x : R, (∀ n : ℕ, ∃ y : R, x = (p : R) ^ n * y) → x = 0) → ∀ f g : ℤ_[p] →+* R, f = g := by
  first | exact @GlobalTheory.padicInt_ringHom_ext_of_separated | exact GlobalTheory.padicInt_ringHom_ext_of_separated | (intros; apply GlobalTheory.padicInt_ringHom_ext_of_separated <;> assumption)
