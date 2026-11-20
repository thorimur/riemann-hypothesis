import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPrismLocalizationAwayOfGenerated
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPrismLocalizationAway_of_generated : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (s d : B.A), GenAway B s d → ∃ (C : Obj l R) (h : Hom B C), IsLoc s h ∧ C.I = Ideal.span {h.f d} := by
  first | exact @GlobalTheory.BSP.exists_isLoc | exact GlobalTheory.BSP.exists_isLoc | (intros; apply GlobalTheory.BSP.exists_isLoc <;> assumption)
