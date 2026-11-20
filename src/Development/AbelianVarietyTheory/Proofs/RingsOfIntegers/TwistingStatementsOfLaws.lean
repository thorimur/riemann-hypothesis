import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinearStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem twisting_statements_of_laws :
    Laws → TwistBaseChangeStatement → TWStatement ∧ FiniteOrderValuationInvariance ∧ PullbackValuationForwardBound := by
  intro hL hT

  have hG : GlobalFnsSt := hL.globalFns
  have hTW : TWStatement := TWM.tw_of hG (twistBCSpan_of hT) GlobalTheory.T.valuation_thetaRatio_eq_bilinear
  exact ⟨hTW, galois_fixed_adelic_matrices_descend hL hTW, pullback_valuation_forward_of (pullGen_of hG) (QuadraticAlgebraValuation.qAl_of hL)⟩

end GlobalTheory
