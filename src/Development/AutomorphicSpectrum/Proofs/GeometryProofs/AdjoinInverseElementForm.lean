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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo

theorem exists_numerator_of_mem_adjoin_insert_inv :
    ∀ (T : Type) (Ω : Type) [Field Ω] [CharZero Ω] (u : T → Ω) (f : Ω) (S : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert f⁻¹ (Set.range u)) → ∀ F : MvPolynomial T ℚ, aeval u F = f → f ≠ 0 → ∀ s : S,
    ∃ (G : MvPolynomial T ℚ) (k : ℕ), (s : Ω) * f ^ k = aeval u G := by
  intro T Ω _ _ u f S hS F hF hf s
  obtain ⟨s, hs⟩ := s
  subst hS
  show ∃ (G : MvPolynomial T ℚ) (k : ℕ), s * f ^ k = aeval u G
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨i, rfl⟩
    · exact ⟨1, 1, by simp [hf]⟩
    · exact ⟨X i, 0, by simp⟩
  | algebraMap q => exact ⟨C q, 0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨G₁, k₁, h₁⟩ := ihx
    obtain ⟨G₂, k₂, h₂⟩ := ihy
    refine ⟨G₁ * F ^ k₂ + G₂ * F ^ k₁, k₁ + k₂, ?_⟩
    simp only [map_add, map_mul, map_pow, hF, ← h₁, ← h₂]
    ring
  | mul x y _ _ ihx ihy =>
    obtain ⟨G₁, k₁, h₁⟩ := ihx
    obtain ⟨G₂, k₂, h₂⟩ := ihy
    refine ⟨G₁ * G₂, k₁ + k₂, ?_⟩
    simp only [map_mul, ← h₁, ← h₂]
    ring

end GlobalTheory.CompanionTheory.Ggeo
