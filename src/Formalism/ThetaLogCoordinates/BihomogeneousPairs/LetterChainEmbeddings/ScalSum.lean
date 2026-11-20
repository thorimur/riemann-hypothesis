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

namespace Formalism.InvariantFactorPaths.KP.LL

open Finset

variable {K : Type} [Field K] [CharZero K]

noncomputable def tU (k A l : ℕ) : K :=
  (-1 : K) ^ l * ((k - 1).choose l : K) * ((A - k - l).factorial : K) / ((A - l).factorial : K)

noncomputable def tV (k A l : ℕ) : K := if l = 0 then 0 else tU k A (l - 1)

noncomputable def tT (k A l : ℕ) : K :=
  (((l.factorial : ℕ) : K) ^ 2 * (((A + 1 - l).choose l : ℕ) : K))⁻¹ *
    ((-1 : K) ^ (k - l) / ((((k - l).factorial : ℕ) : K) ^ 2 * (((A - 2 * l).choose (k - l) : ℕ) : K)))

end Formalism.InvariantFactorPaths.KP.LL
