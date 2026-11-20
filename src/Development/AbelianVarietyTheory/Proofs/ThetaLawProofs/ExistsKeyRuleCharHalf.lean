import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubringsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleExistsOfAlgebraicInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIntegralKeyInvariantRuleCharZeroStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTop

theorem exists_keyRule_charHalf :
    Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic →
      ∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf := by
  intro hL hT hI hP hTor
  have hD : KeyDesc := (GlobalTheory.T.keyData_descend_countable_subrings hL).2
  exact GlobalTheory.T.thetaKeyRule_exists_of_algebraic_invariants hL hT hI hP hTor (GlobalTheory.T.exists_integralKeyInvariantRule_charZero hL hT hTor hD) hD

end GlobalTheory.KeyTop
