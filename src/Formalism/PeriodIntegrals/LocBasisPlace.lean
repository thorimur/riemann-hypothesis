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

def LocBasisPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ρ : E →+* ℂ_[p]) (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)), L.FG → Submodule.span E (L : Set (Fin N → E)) = ⊤ →
    ∃ P : Matrix (Fin N) (Fin N) E, P.det ≠ 0 ∧
      (∀ a, ∃ s : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ s • P.transpose a ∈ L) ∧
      ∀ x ∈ L, ∃ s : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 E, s • x = ∑ a, c a • P.transpose a

end PI
