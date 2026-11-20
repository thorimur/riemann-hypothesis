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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Matrix

namespace GlobalTheory

theorem laurent_poly_eval_of_laurent :
    ∀ (σ : Type) (g : σ → ℂ → ℂ), (∀ a, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 → t ^ N * g a t = p.eval t) →
      ∀ Q : MvPolynomial σ ℂ, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 →
        t ^ N * MvPolynomial.eval (fun a => g a t) Q = p.eval t := by
  intro σ g hg Q
  induction Q using MvPolynomial.induction_on
  · rename_i c
    exact ⟨0, Polynomial.C c, fun t _ => by simp⟩
  · rename_i p q hp hq
    obtain ⟨N₁, P₁, h₁⟩ := hp
    obtain ⟨N₂, P₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, Polynomial.X ^ N₂ * P₁ + Polynomial.X ^ N₁ * P₂, fun t ht => ?_⟩
    simp only [map_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h₁ t ht, ← h₂ t ht]
    ring
  · rename_i p a hp
    obtain ⟨N, P, h⟩ := hp
    obtain ⟨N', P', h'⟩ := hg a
    refine ⟨N + N', P * P', fun t ht => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X, Polynomial.eval_mul]
    rw [← h t ht, ← h' t ht]
    ring

end GlobalTheory
