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

namespace PI

open NumberField

def ChiExCM : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
    ∀ (S : Type) [Fintype S] (emb : S → E →+* ℂ), (∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ s, emb s x = 1) →
    ∃ χ : Submodule (𝓞 E) E → ℂ,
      (∀ 𝔞 𝔟 : Submodule (𝓞 E) E, (∃ 𝔞' : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔞' ↔ c x ∈ 𝔞) ∧ 𝔞 * 𝔞' = 1) →
        (∃ 𝔟' : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔟' ↔ c x ∈ 𝔟) ∧ 𝔟 * 𝔟' = 1) → χ (𝔞 * 𝔟) = χ 𝔞 * χ 𝔟) ∧
      ∀ z : E, z * c z = 1 → χ (Submodule.span (𝓞 E) {z}) = ∏ s, (emb s z)⁻¹

end PI
