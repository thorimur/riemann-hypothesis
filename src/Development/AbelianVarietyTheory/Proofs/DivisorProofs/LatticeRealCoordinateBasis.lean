import Mathlib.Algebra.Module.ZLattice.Basic
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

open Module

theorem GlobalTheory.exists_zlattice_basis_realCoord_integral : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∃ (n : ℕ) (b : Fin n → Λ) (c : Fin n → (Fin g → ℂ) →ₗ[ℝ] ℝ),
      (∀ v, ∑ i, c i v • ((b i : Λ) : Fin g → ℂ) = v) ∧
      ∀ (φ : Λ →+ (Fin g → ℂ)) (x : Λ), ∑ i, c i (x : Fin g → ℂ) • φ (b i) = φ x := by
  intro g Λ hd hs
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let bZ0 := Module.Free.chooseBasis ℤ Λ
  let bZ := bZ0.reindex (Fintype.equivFin _)
  let bR := bZ.ofZLatticeBasis ℝ Λ
  refine ⟨_, fun i => bZ i, fun i => bR.coord i, ?_, ?_⟩
  · intro v
    have h := bR.sum_repr v
    conv_rhs => rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [bR]
  · intro φ x
    have hx : ∀ i, bR.coord i (x : Fin g → ℂ) = ((bZ.repr x i : ℤ) : ℝ) := by
      intro i
      simp [bR, Module.Basis.ofZLatticeBasis_repr_apply]
    simp_rw [hx]
    conv_rhs => rw [← bZ.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul, map_zsmul]
