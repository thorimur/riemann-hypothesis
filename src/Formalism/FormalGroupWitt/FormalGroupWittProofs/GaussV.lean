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
import Mathlib.RingTheory.MvPowerSeries.Basic
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

noncomputable section

universe u

namespace Formalism.FG.BernoulliBounds

open MvPowerSeries Formalism.G Formalism.FG.SolveVAux

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def BndLe {ι : Type*} (c : ℝ) (M : ℕ) (f : MvPowerSeries ι K) (B : ℝ) : Prop :=
  ∀ t : ι →₀ ℕ, t.degree ≤ M → ‖coeff t f‖ * c ^ t.degree ≤ B

variable [CharZero K]

def shiftPoly (K : Type u) [Field K] (l m : ℕ) (j : ZMod m) (N : ℕ) : MvPowerSeries (ZMod m) K :=
  ∑ e ∈ Finset.range (N + 1), ((l : K) ^ e)⁻¹ • (X (j - (e : ZMod m)) ^ ((l ^ 2) ^ e))

end Formalism.FG.BernoulliBounds

namespace Formalism.FG

end Formalism.FG
