import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedStatus
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJUnram

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

theorem cm2 (hH : _root_.Neutral.HilbertClassField.Statement) (hC : ChebOmSt) : CM2 :=
  goodReduction_of_integral_unramified jInt (jUnram hH hC)

end ReciprocityTheory.ChartRestriction.L1
