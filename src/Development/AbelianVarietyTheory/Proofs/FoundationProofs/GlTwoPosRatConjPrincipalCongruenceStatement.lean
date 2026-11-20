import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatConjPrincipalCongruence
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glTwoPosRat_conj_principal_congruence : ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ N : ℕ, ∀ δ ∈ CongruenceSubgroup.Gamma (N * n), ∃ δ' ∈ CongruenceSubgroup.Gamma N, g * ofSL δ = ofSL δ' * g := by
  first | exact @GlobalTheory.FN.exists_conj_principal_congruence | exact GlobalTheory.FN.exists_conj_principal_congruence | (intros; apply GlobalTheory.FN.exists_conj_principal_congruence <;> assumption)
