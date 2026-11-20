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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

theorem card_dotProduct_eq_one :
    ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a : Fin (n + 1) → k), a ≠ 0 →
  Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  intro k _ _ n a ha
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  have hax₀ : a ⬝ᵥ Pi.single i (a i)⁻¹ = 1 := by
    rw [dotProduct_single, mul_inv_cancel₀ hi]
  have hfib : ∀ c : k, (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = c)).card =
      (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card := by
    intro c
    apply Finset.card_bij' (fun x _ => x + (1 - c) • Pi.single i (a i)⁻¹)
      (fun x _ => x - (1 - c) • Pi.single i (a i)⁻¹)
    case hi =>
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [dotProduct_add, dotProduct_smul, hax₀, hx, smul_eq_mul, mul_one]
      ring
    case hj =>
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [dotProduct_sub, dotProduct_smul, hax₀, hx, smul_eq_mul, mul_one]
      ring
    case left_inv =>
      intro x _
      simp
    case right_inv =>
      intro x _
      simp
  have htot : (Finset.univ : Finset (Fin (n + 1) → k)).card =
      ∑ c : k, (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (a ⬝ᵥ x))
  have hcard : (Finset.univ : Finset (Fin (n + 1) → k)).card = Fintype.card k ^ (n + 1) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [← hcard, htot, Finset.sum_congr rfl (fun c _ => hfib c), Finset.sum_const,
    Finset.card_univ, smul_eq_mul]

end GlobalTheory.CompanionTheory.GapOpCount
