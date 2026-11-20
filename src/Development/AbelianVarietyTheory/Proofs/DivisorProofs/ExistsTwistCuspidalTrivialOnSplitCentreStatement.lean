import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistCuspidalTrivialOnSplitCentre
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twist_cuspidal_trivial_on_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, ∃ χ : HChar E, GlobalTheory.DiscSpec.IsNormalised (π.twist χ) := by
  first | exact @GlobalTheory.GKNorm.exists_twist_isNormalised | exact GlobalTheory.GKNorm.exists_twist_isNormalised | (intros; apply GlobalTheory.GKNorm.exists_twist_isNormalised <;> assumption)
