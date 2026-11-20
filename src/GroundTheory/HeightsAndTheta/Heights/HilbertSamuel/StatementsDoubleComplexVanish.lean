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

def DoubleComplexVanish.Statement : Prop :=
  ∀ (C : ℕ → ℕ → Type) [∀ p n, AddCommGroup (C p n)] (P : ∀ p n, AddSubgroup (C p n))
    (δ : ∀ p n, C p n →+ C p (n + 1)) (κ : ∀ p n, C (p + 1) n →+ C p n) (R : ℕ),
    (∀ p n, ∀ x ∈ P p n, δ p n x ∈ P p (n + 1)) →
    (∀ p n, ∀ x ∈ P (p + 1) n, κ p n x ∈ P p n) →
    (∀ p n, ∀ x ∈ P p n, δ p (n + 1) (δ p n x) = 0) →
    (∀ p n, ∀ x ∈ P (p + 1) n, δ p n (κ p n x) = κ p (n + 1) (δ (p + 1) n x)) →
    (∀ p n, ∀ x ∈ P (p + 2) n, κ p n (κ (p + 1) n x) = 0) →
    (∀ n, ∀ x ∈ P 0 n, ∃ y ∈ P 1 n, κ 0 n y = x) →
    (∀ p n, ∀ x ∈ P (p + 1) n, κ p n x = 0 → ∃ y ∈ P (p + 2) n, κ (p + 1) n y = x) →
    (∀ p n, R < p → ∀ x ∈ P p n, x = 0) →
    (∀ p, 1 ≤ p → p ≤ R → ∀ n, ∀ x ∈ P p (n + 1), δ p (n + 1) x = 0 → ∃ y ∈ P p n, δ p n y = x) →
    ∀ n, ∀ x ∈ P 0 (n + 1), δ 0 (n + 1) x = 0 → ∃ y ∈ P 0 n, δ 0 n y = x

def DoubleComplexVanish.exP (p n : ℕ) : AddSubgroup ℤ := if p ≤ 1 ∧ n = 0 then ⊤ else ⊥

def DoubleComplexVanish.exκ (p : ℕ) : ℤ →+ ℤ := if p = 0 then AddMonoidHom.id ℤ else 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
