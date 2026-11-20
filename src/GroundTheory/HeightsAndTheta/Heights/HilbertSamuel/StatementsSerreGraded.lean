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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def gradedSpan {Ω : Type*} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω) (n : ℕ) :
    AddSubgroup Ω :=
  AddSubgroup.closure {x | ∃ (l : Fin r) (μ : Fin q → ℕ), d l + ∑ j, μ j = n ∧ x = t l * ∏ j, w j ^ μ j}

def SerreGraded.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (q r : ℕ) (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω),
    (∃ j, w j ≠ 0) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ s : Ω,
      (∀ j, w j ≠ 0 → ∃ D : ℕ, s * w j ^ D ∈ gradedSpan w d t (n + D)) → s ∈ gradedSpan w d t n

theorem gradedSpan_gen_mem {Ω : Type*} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
    (l : Fin r) (μ : Fin q → ℕ) : t l * ∏ j, w j ^ μ j ∈ gradedSpan w d t (d l + ∑ j, μ j) :=
  AddSubgroup.subset_closure ⟨l, μ, rfl, rfl⟩

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
