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
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.GenUnr

variable {O : Type} [CommRing O]

noncomputable def red (I : Ideal O) (r : ℕ) : (Fin r → O) →ₗ[O] (Fin r → O ⧸ I) :=
  ((Ideal.Quotient.mkₐ O I).toLinearMap).compLeft (Fin r)

noncomputable def rowSpan {n r : ℕ} (I : Ideal O) (z : Matrix (Fin n) (Fin r) O) :
    Submodule O (Fin r → O ⧸ I) :=
  Submodule.span O (Set.range fun i => red I r (z i))

end GlobalTheory.GenUnr

namespace GlobalTheory.GenUnr
open Matrix
variable {O : Type} [CommRing O]

end GlobalTheory.GenUnr

namespace GlobalTheory.GenUnr
open Matrix

end GlobalTheory.GenUnr

namespace GlobalTheory.GenUnr
open Matrix

end GlobalTheory.GenUnr
