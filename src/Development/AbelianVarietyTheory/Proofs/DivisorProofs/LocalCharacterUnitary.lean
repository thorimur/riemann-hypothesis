import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.LocalField.Basic
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
open ValuativeRel
open scoped Matrix Topology

namespace GlobalTheory

theorem addChar_norm_eq_one_of_continuous {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (x : k) : ‖ψ0 x‖ = 1 := by
  have hK : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hbd : ∀ y : k, ∃ C : ℝ, ∀ n : ℕ, ‖ψ0 y‖ ^ n ≤ C := by
    intro y
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (f := fun o : k => ψ0 (o * y)) (by fun_prop)
    refine ⟨C, fun n => ?_⟩
    have := hC (n : k) (natCast_mem _ n)
    rwa [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at this
  have hle : ∀ y : k, ‖ψ0 y‖ ≤ 1 := by
    intro y
    obtain ⟨C, hC⟩ := hbd y
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    exact absurd (hC n) (not_le.2 hn)
  have hmul : ‖ψ0 x‖ * ‖ψ0 (-x)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  have h1 := hle x
  have h2 := hle (-x)
  have h3 := norm_nonneg (ψ0 x)
  have h4 := norm_nonneg (ψ0 (-x))
  nlinarith

theorem addChar_norm_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ∀ x : k, ‖ψ0 x‖ = 1 :=
  fun ψ0 hψ x => addChar_norm_eq_one_of_continuous ψ0 hψ x

end GlobalTheory
