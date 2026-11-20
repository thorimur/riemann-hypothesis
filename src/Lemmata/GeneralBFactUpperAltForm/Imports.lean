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
import Mathlib.RingTheory.WittVector.IsPoly
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

namespace Bl.general_b_fact_upper_alt_form

theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] {n k : Type} [Fintype.{0} n] [DecidableEq.{1} n] [inst_3 : Fintype.{0} k]
  [DecidableEq.{1} k] (f : RingHom.{0, 0} K Complex) (A : Matrix.{0, 0, 0} n k K),
  Function.Injective.{1, 1} (Matrix.mulVec.{0, 0, 0} A) →
    Function.Injective.{1, 1} (Matrix.mulVec.{0, 0, 0} (Matrix.map.{0, 0, 0, 0} A (DFunLike.coe.{1, 1, 1} f))) := by
  intro K _ n k _ _ _ _ f A hA
  have hker : LinearMap.ker (Matrix.toLin' A) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fun x y hxy => hA (by simpa only [Matrix.toLin'_apply] using hxy))
  obtain ⟨g, hg⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective hker
  have hBA : LinearMap.toMatrix' g * A = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h
  have h1 : (LinearMap.toMatrix' g).map f * A.map f = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ f.map_zero f.map_one]
  intro v w hvw
  have h2 := congrArg (fun u => Matrix.mulVec ((LinearMap.toMatrix' g).map f) u) hvw
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using h2

end Bl.general_b_fact_upper_alt_form
