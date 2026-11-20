import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfCocycleSolutionTeichmullerEpsilonRootPow
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfCocycleSolution_teichmullerEpsilonRoot_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ), Lev l s → ∀ g : GQ l, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ U : ℤ_[l], (l : ℤ_[l]) ^ s ∣ U - 1 → ∀ m : ℕ, ¬ l ∣ m → Solv AI K s g U (epsT AI s ^ m) := by
  first | exact @GlobalTheory.ExpImage.EpsSolve.main | exact GlobalTheory.ExpImage.EpsSolve.main | (intros; apply GlobalTheory.ExpImage.EpsSolve.main <;> assumption)
