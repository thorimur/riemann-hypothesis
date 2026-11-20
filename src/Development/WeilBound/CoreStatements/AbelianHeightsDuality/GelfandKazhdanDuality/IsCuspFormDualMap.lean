import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace PositivityTheory.PRW.GKD

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

abbrev invA : GA E a →* GA E a := invT a (Ad E)

theorem invA_invA (g : GA E a) : invA E a (invA E a g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose g.val

end PositivityTheory.PRW.GKD

end
