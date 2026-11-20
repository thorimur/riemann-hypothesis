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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory

theorem exists_basis_over_embedding (K : Type) [Field K] (σ₀ : K →+* ℂ) (m : ℕ)
    (a : Fin m → ℂ) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (c : Fin m → Fin n → K),
      (∀ t : Fin n → K, ∑ b, σ₀ (t b) * e b = 0 → t = 0) ∧
        ∀ i, a i = ∑ b, σ₀ (c i b) * e b := by
  letI : Algebra K ℂ := σ₀.toAlgebra
  have hs : ∀ (k : K) (z : ℂ), k • z = σ₀ k * z := fun k z => rfl
  let V : Submodule K ℂ := Submodule.span K (Set.range a)
  haveI : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range a)
  let B := Module.finBasis K V
  have ha : ∀ i, a i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Module.finrank K V, fun b => (B b : ℂ), fun i b => B.repr ⟨a i, ha i⟩ b, ?_, ?_⟩
  · intro t ht
    have hli := Fintype.linearIndependent_iff.1 B.linearIndependent t
    funext b
    refine hli ?_ b
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, hs, Submodule.coe_zero]
    exact ht
  · intro i
    have h := congrArg (Subtype.val : V → ℂ) (B.sum_repr ⟨a i, ha i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hs] at h
    exact h.symm

end GlobalTheory
