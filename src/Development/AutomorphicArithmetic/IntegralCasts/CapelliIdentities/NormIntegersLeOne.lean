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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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

theorem UpperTheory.norm_integers_le_one :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact (Nat.Prime l)] (e : K →+* PadicAlgCl l) (x : NumberField.RingOfIntegers K), ‖e (algebraMap (NumberField.RingOfIntegers K) K x)‖ ≤ 1 := by
  intro K _ _ l _ e x
  have hx : IsIntegral ℤ (e (algebraMap (NumberField.RingOfIntegers K) K x)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map e.toIntAlgHom
  generalize e (algebraMap (NumberField.RingOfIntegers K) K x) = y at hx
  let S : Subring (PadicAlgCl l) := (NormedField.valuation (K := PadicAlgCl l)).integer
  have hS : IsIntegral S y := hx.tower_top
  have h := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral hS
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h
