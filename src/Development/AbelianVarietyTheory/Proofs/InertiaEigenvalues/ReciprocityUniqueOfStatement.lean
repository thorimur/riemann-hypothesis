import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityUniqueOf
open GlobalTheory.Published GlobalTheory.TheRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reciprocity_unique_of : LocalLanglandsExists → LocalConverseGL → LanglandsExhaustionGL → IrreducibleAdmissibleGL → StandardFunctorsFiniteLength → RecUnique := by
  first | exact @GlobalTheory.TheRec.recUnique_of_localConverse | exact GlobalTheory.TheRec.recUnique_of_localConverse | (intros; apply GlobalTheory.TheRec.recUnique_of_localConverse <;> assumption)
