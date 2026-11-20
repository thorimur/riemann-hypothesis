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

theorem UpperTheory.ConvolutionTheory.K.autOrder :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K ≃+* K), ∃ m : ℕ, 0 < m ∧ σ ^ m = 1 := by
  intro K _ _ σ
  let τ : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := σ) (fun x => by simp)
  refine ⟨orderOf τ, orderOf_pos τ, ?_⟩
  have h : ∀ m : ℕ, ∀ x, (σ ^ m) x = (τ ^ m) x := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [pow_succ, pow_succ]; exact ih _
  ext x
  rw [h, pow_orderOf_eq_one]
  rfl
