import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

theorem linRoot_pow_homog_lower {ι : Type} [Fintype ι] {N : ℕ} (u : ι → Fin N → ℝ) (n : ℕ) :
    (linRoot u ^ n).IsHomogeneous n := by
  have h : (linRoot u).IsHomogeneous 1 := by
    unfold linRoot
    have h1 : (∑ x : ι × Fin N, C (u x.1 x.2) * X x : MvPolynomial (ι × Fin N) ℝ).IsHomogeneous 1 := by
      apply IsHomogeneous.sum
      intro x _
      simpa using (isHomogeneous_C _ (u x.1 x.2)).mul (isHomogeneous_X ℝ x)
    exact h1.neg
  simpa using h.pow n

end GlobalTheory.Mean4
