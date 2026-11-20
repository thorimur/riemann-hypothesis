import Mathlib.Algebra.Module.ZLattice.Basic
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

open Module
open scoped InnerProductSpace

noncomputable section

namespace PI

def TransferenceCover : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ), 0 < lam →
    (∀ y : E, y ≠ 0 → (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) → lam ≤ ‖y‖) →
    ∀ x : E, ∃ l ∈ Λ, ‖x - l‖ * lam ≤ (finrank ℝ E : ℝ) / 2

def succMin {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin i → EuclideanSpace ℝ (Fin N),
    (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}

def dualZ {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Submodule ℤ (EuclideanSpace ℝ (Fin N)) where
  carrier := {x | ∀ y ∈ M, ∃ z : ℤ, ⟪x, y⟫_ℝ = z}
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨z1, h1⟩ := ha y hy
    obtain ⟨z2, h2⟩ := hb y hy
    exact ⟨z1 + z2, by rw [inner_add_left, h1, h2]; push_cast; ring⟩
  zero_mem' := fun y _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha y hy
    obtain ⟨z, h⟩ := ha y hy
    exact ⟨c * z, by rw [← Int.cast_smul_eq_zsmul ℝ c a, real_inner_smul_left, h]; push_cast; ring⟩

def TransferenceMinima : Prop :=
  ∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))),
    DiscreteTopology M → Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ →
    ∀ i, 1 ≤ i → i ≤ N → succMin M i * succMin (dualZ M) (N + 1 - i) ≤ N

end PI
