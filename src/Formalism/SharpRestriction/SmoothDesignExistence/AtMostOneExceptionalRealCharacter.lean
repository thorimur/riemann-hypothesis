import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes

noncomputable section

namespace Formalism.MainNotions.Pk.SD

open Formalism.BasicNotions Formalism.MainNotions.S

structure RowsG {eps : ℝ} (Fm : FamP eps) : Prop where

  b5rec : ShortIntervalPrimes.FamilyPrimesAsPropTwoFive Fm
  b7rec : ShortIntervalPrimes.FamilyPrimesAsPropTwoSeven Fm

  familyRankBoundFourth : ShortIntervalPrimes.FamilyAdmittedLemmaFour Fm
  familyRankBoundEighth : ShortIntervalPrimes.FamilyTemperatureAsymptotic Fm

end Formalism.MainNotions.Pk.SD

end
