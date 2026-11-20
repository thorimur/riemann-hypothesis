import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
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

open scoped Classical

namespace PositivityTheory.Rg.BcB.F

def PowerBoundNonzeroCoefficient : Prop := ∀ (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
  (ι : Type) [Fintype ι] [Nonempty ι] (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] (R : ∀ s, B →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (J : Type) [Fintype J] (c : J → ℂ) (q : J → (B →ₐ[ℂ] ℂ)),
  (∀ b, ∃ (C : ℝ) (N : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖∑ j, c j * q j b ^ k‖ ≤ C * (1 + k) ^ N * (Finset.univ.sup' Finset.univ_nonempty fun s => ‖R s b‖) ^ k) →
  ∀ p : B →⋆ₐ[ℂ] ℂ, ∑ j with q j = (p : B →ₐ[ℂ] ℂ), c j ≠ 0 → ∃ s, ∀ b, ‖p b‖ ≤ ‖R s b‖

end PositivityTheory.Rg.BcB.F

end
