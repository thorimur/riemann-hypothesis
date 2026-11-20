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

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem transposedRegularRep_ringHom_trace :
    ∀ (O : Type) [CommRing O] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ)
      (b : Module.Basis (Fin n) R Λ) (φ : R →+* O),
      (∃ ρ : Λ →+* Matrix (Fin n) (Fin n) O,
        ⇑ρ = fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) ∧
      ∀ a : Λ, (((Algebra.leftMulMatrix b a).transpose).map φ).trace
        = φ (Algebra.trace R Λ a) := by
  intro O _ R Λ _ _ _ n b φ
  refine ⟨⟨{ toFun := fun a => ((Algebra.leftMulMatrix b a).transpose).map φ
             map_one' := ?_
             map_mul' := ?_
             map_zero' := ?_
             map_add' := ?_ }, rfl⟩, ?_⟩
  · rw [map_one, Matrix.transpose_one]
    exact Matrix.map_one φ (map_zero φ) (map_one φ)
  · intro x y
    rw [mul_comm x y, map_mul, Matrix.transpose_mul, Matrix.map_mul]
  · ext i j
    simp
  · intro x y
    rw [map_add, Matrix.transpose_add]
    ext i j
    simp
  · intro a
    rw [Algebra.trace_eq_matrix_trace b a, ← Matrix.trace_transpose (Algebra.leftMulMatrix b a)]
    simp [Matrix.trace, map_sum]

end GlobalTheory
