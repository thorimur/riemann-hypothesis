import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfCocycleRecursionOfFrobeniusTwist
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainfCocycleRecursion_of_frobenius_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (U : ℤ_[l]) (k : ℕ) (β η : Ainf l), Step AI g U AI.μ k (WittVector.frobenius β - AI.ξ ^ k * β) (WittVector.frobenius η - AI.ξ ^ k * η) → ∃ z : ℤ_[l], Step AI g U AI.π₁ k β (η + algebraMap ℤ_[l] (Ainf l) z * AI.π₁ ^ k) := by
  first | exact @GlobalTheory.ExpStep.main | exact GlobalTheory.ExpStep.main | (intros; apply GlobalTheory.ExpStep.main <;> assumption)
