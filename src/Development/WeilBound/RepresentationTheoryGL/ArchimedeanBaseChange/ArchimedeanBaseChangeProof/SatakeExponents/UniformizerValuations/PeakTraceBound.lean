import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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

noncomputable section

namespace PositivityTheory.Rg.BcB.F

def PeakTraceBound : Prop := ∀ (A : Type) [CommRing A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (ι : Type) [Fintype ι] [Nonempty ι] (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] (R : ∀ s, A →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ)
  (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (u : Module.End ℂ V)
  (p : A →⋆ₐ[ℂ] ℂ) (a₀ : A),
  (∀ s g, Commute (β s) (R s g)) → (∀ g, Commute u (ρ g)) → p a₀ ≠ 0 →
  (∀ g ∈ Ideal.span {a₀}, ∃ (C : ℝ) (N j : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖LinearMap.trace ℂ V ((u * ρ g) ^ k)‖ ≤ C * (1 + k) ^ N *
      Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * R s g) ^ (k - j)‖)) →
  (∃ v : V, v ≠ 0 ∧ u v = v ∧ ∀ g, ρ g v = p g • v) →
  ∃ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (R s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
    (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) ∧
    (∀ g, χ ⟨R s g, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ = p g) ∧
    χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0

end PositivityTheory.Rg.BcB.F

end
