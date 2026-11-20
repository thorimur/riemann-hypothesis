import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

noncomputable def UpperTheory.Reformulated.B.MultiplicationFunction.mulFn.{u_1} :
    {X : Type u_1} →
      [inst : MeasurableSpace X] →
        {ν : MeasureTheory.Measure X} →
          (c : X → ℝ) →
            Measurable c →
              (∀ (x : X), |c x| ≤ (1 : ℝ)) → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) :=
  fun {X} _ {ν} c hc hb f =>
    MeasureTheory.MemLp.toLp (fun x : X => (c x : ℂ) * f x)
      (MeasureTheory.MemLp.of_le (MeasureTheory.Lp.memLp f)
        ((Complex.measurable_ofReal.comp hc).aestronglyMeasurable.mul
          (MeasureTheory.Lp.aestronglyMeasurable f))
        (Filter.Eventually.of_forall fun x => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) (hb x)) :
        MeasureTheory.MemLp (fun x : X => (c x : ℂ) * f x) 2 ν)
