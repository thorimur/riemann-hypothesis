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

namespace ReciprocityTheory.ChartRestriction.G.AR

def multiLt (D a : ℕ) : Finset (Fin D → ℕ) :=
  (Finset.range a).biUnion (fun d => Finset.Nat.antidiagonalTuple D d)

def JetIndepStatement.{u, v, w} : Prop :=
  ∀ (K : Type u) (A : Type v) (H : Type w) [Field K] [CommRing A] [Algebra K A]
    [AddCommGroup H] [Module A H] [Module K H] [IsScalarTower K A H]
    (J : Ideal A) (D a0 T δ : ℕ) (s : Fin D → A) (w0 : A) (t : Fin δ → H),
    (∀ k, s k ∈ J) →
    (∀ a < a0, ∀ h : (Fin D → ℕ) → H,
      (∑ α ∈ Finset.Nat.antidiagonalTuple D a, (∏ k, s k ^ α k) • h α) ∈ (J ^ (a + 1)) • (⊤ : Submodule A H) →
      ∀ α ∈ Finset.Nat.antidiagonalTuple D a, h α ∈ J • (⊤ : Submodule A H)) →
    (∃ u : A, u * w0 - 1 ∈ J) →
    (∀ c : Fin δ → K, (∑ i, c i • t i) ∈ J • (⊤ : Submodule A H) → c = 0) →
    ∀ c : (Fin D → ℕ) → Fin δ → K,
      (∑ α ∈ multiLt D a0, ∑ i, c α i • (((∏ k, s k ^ α k) * w0 ^ (T - ∑ k, α k)) • t i)) ∈
          (J ^ a0) • (⊤ : Submodule A H) →
      ∀ α ∈ multiLt D a0, ∀ i, c α i = 0

end ReciprocityTheory.ChartRestriction.G.AR
