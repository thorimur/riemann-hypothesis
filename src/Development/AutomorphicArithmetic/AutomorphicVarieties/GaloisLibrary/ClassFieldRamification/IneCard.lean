import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
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

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineCard :
    (∀ (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L] [IsGalois k L] (w : HeightOneSpectrum (𝓞 L)), Nat.card (w.asIdeal.inertia Gal(L/k)) = w.asIdeal.ramificationIdx (𝓞 k)) ∧ ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (w : HeightOneSpectrum (𝓞 L)), Nat.card (w.asIdeal.inertia Gal(L/ℚ)) = w.asIdeal.ramificationIdx ℤ := by
  refine ⟨fun k L _ _ _ _ _ _ w => ?_, fun L _ _ _ w => ?_⟩
  · rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under (𝓞 k)) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under (𝓞 k)) w.asIdeal Gal(L/k)]
  · rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under ℤ) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal Gal(L/ℚ)]
