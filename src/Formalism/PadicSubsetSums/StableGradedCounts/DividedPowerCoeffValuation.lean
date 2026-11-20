import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial TensorProduct

theorem natLog_le_logb (l n : ℕ) (hl : 2 ≤ l) (hn : 1 ≤ n) : (Nat.log l n : ℝ) ≤ Real.logb l n := by
  have h1 : (l : ℝ) ^ (Nat.log l n) ≤ n := by exact_mod_cast Nat.pow_log_le_self l (by omega)
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  rw [Real.le_logb_iff_rpow_le hl' (by exact_mod_cast hn), Real.rpow_natCast]
  exact h1

section Frame

open scoped Matrix

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

end Frame

end Formalism.IrreducibleCountingLemmas.WindowSums
