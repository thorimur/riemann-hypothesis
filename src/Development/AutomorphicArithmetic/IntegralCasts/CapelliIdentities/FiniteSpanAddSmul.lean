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

theorem UpperTheory.finite_span_add_smul :
    ∀ {ι V : Type} [AddCommGroup V] [Module ℂ V] (T : ι → V →ₗ[ℂ] V) (S : Set ι) (a b : V) (z : ℂ),
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i a) '' S)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i b) '' S)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i (a + z • b)) '' S)) := by
  intro ι V _ _ T S a b z ha hb
  have hle : Submodule.span ℂ ((fun i => T i (a + z • b)) '' S) ≤
      Submodule.span ℂ ((fun i => T i a) '' S) ⊔ Submodule.span ℂ ((fun i => T i b) '' S) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [map_add, map_smul, SetLike.mem_coe]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, hi, rfl⟩)
      (Submodule.smul_mem _ z (Submodule.subset_span ⟨i, hi, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle
