import Mathlib.Algebra.Module.ZLattice.Covolume
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

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory

noncomputable section

variable (Q V K : Type*) [AddCommGroup Q] [Module ℚ Q] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype K]

def IntegralFormCovolume.Statement : Prop :=
  ∀ (ψ : Q →+ V) (e : Basis K ℚ Q) (T : LinearMap.BilinForm ℚ Q) (μ : Measure V),
    μ.IsAddHaarMeasure → T.Nondegenerate → LinearIndependent ℝ (fun k => ψ (e k)) →
    finrank ℝ V = Fintype.card K →
    ∃ C : ℝ, ∀ (L : AddSubgroup Q) (k : ℤ), k ≠ 0 → L.FG → Submodule.span ℚ (L : Set Q) = ⊤ →
      (∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, T x y = n) →
      (∀ y : Q, (∀ x ∈ L, ∃ n : ℤ, T y x = n) → k • y ∈ L) →
      ∃ _ : DiscreteTopology (AddSubgroup.toIntSubmodule (L.map ψ)),
        IsZLattice ℝ (AddSubgroup.toIntSubmodule (L.map ψ)) ∧
        ZLattice.covolume (AddSubgroup.toIntSubmodule (L.map ψ)) μ ^ 2 ≤
          C * |(k : ℝ)| ^ Fintype.card K

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
