import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRings
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoDimensionFormula_concretePeriodRings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)], BlochKatoDim (P.PD K) ↥LL.1 := by
  first | exact @GlobalTheory.BlochKatoTied.blochKatoDim_of_tied | exact GlobalTheory.BlochKatoTied.blochKatoDim_of_tied | (intros; apply GlobalTheory.BlochKatoTied.blochKatoDim_of_tied <;> assumption)
