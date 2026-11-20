import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ESecStruct
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationBaseChangeStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem uniformisationLaws_of_baseChange_laws :
    PolBaseChangeSt → GlobalFnsSt → SecBaseChangeSt → DVR.TwistBaseChangeStatement → Laws4 :=
  fun h₁ h₂ h₃ h₄ => ⟨GlobalTheory.T.uniformisation_baseChange h₁ h₂ h₃ h₄, WeightPf.weightIndep, TLinPf.tLin_of h₂⟩

end GlobalTheory
