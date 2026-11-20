import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes.FamilySizesEpsilon

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ShortIntervalPrimes Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

section Cyc

open NumberField Ideal

end Cyc

def QC (C1 : ℝ) : Prop :=
  ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset ZPt,
    (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧
      DirichletCharacter.LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) →
    ((∑ p ∈ T, analyticOrderNatAt (DirichletCharacter.LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤
      C1 * Q ^ ((1 : ℝ) / 4)

end Formalism.MainNotions.ShortIntervalPrimes.FamilySizesEpsilon

end
