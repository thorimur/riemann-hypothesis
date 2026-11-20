import Formalism.GaussJetBounds.Statement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem coreL_dot_fintype {ι : Type v} [Fintype ι] (n : ι →₀ ℕ) (r : ι → ℝ) :
    dot n r = ∑ i, (n i : ℝ) * r i := by
  unfold dot
  exact Finsupp.sum_fintype _ _ (by simp)

end Formalism.DworkPowerSeriesWeights
