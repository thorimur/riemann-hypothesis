import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnity
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLevelExpansionLaws_of_rootsOfUnity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; LevLaws W := by
  first | exact @GlobalTheory.NL.Expansion.levLaws | exact GlobalTheory.NL.Expansion.levLaws | (intros; apply GlobalTheory.NL.Expansion.levLaws <;> assumption)
