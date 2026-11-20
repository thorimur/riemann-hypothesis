import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnits
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units : Nontrivial Mero ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (a : Mero) = (b : Mero) → ∀ z ∈ Hs, a z = b z) ∧ ∀ a : ℂ → ℂ, DifferentiableOn ℂ a Hs → (a : Mero) ≠ 0 → (∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0) ∧ IsUnit (a : Mero) := by
  first | exact @GlobalTheory.FN.germ_main | exact GlobalTheory.FN.germ_main | (intros; apply GlobalTheory.FN.germ_main <;> assumption)
