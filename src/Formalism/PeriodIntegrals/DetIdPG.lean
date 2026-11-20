import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.NumberTheory.Padics.Complex
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

open NumberField

namespace PI

namespace DetIdPG

def stdH (E : Type) [Field E] [StarRing E] (N : ℕ) (x y : Fin N → E) : E := ∑ i, star (x i) * y i

def IsSDLat (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, stdH E N x y ∈ (algebraMap (𝓞 E) E).range

end DetIdPG

def DetIdPG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) →
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (L L₀ : Submodule (𝓞 E) (Fin N → E)), DetIdPG.IsSDLat E N L → DetIdPG.IsSDLat E N L₀ →
    (∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, (s : E) • x ∈ L₀) ∧ ∀ x ∈ L₀, (s : E) • x ∈ L) →
    ∃ (h : ℕ) (z : E), 0 < h ∧ star z * z = 1 ∧ z * star z = 1 ∧ (∀ ψ : E →+* ℂ_[p], ‖ψ z‖ = 1) ∧
      (Submodule.span (𝓞 E) {x : E | ∃ A : Matrix (Fin N) (Fin N) E, (∀ v ∈ L₀, A.mulVec v ∈ L) ∧ x = A.det}) ^ h =
        Submodule.span (𝓞 E) {z}

end PI
