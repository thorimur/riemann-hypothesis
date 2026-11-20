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

open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure IsCplAt (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B]
    [Algebra R B] : Prop where
  noeth : IsNoetherianRing B
  complete : IsAdicComplete (maximalIdeal B) B
  comap_eq : (maximalIdeal B).comap (algebraMap R B) = p
  dense : ∀ (n : ℕ) (b : B), ∃ a s : R, s ∉ p ∧
    algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n
  strict : ∀ (n : ℕ) (a : R), algebraMap R B a ∈ maximalIdeal B ^ n → ∃ s : R, s ∉ p ∧ s * a ∈ p ^ n

theorem IsCplAt.isPrime {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) : p.IsPrime := by
  rw [← h.comap_eq]
  exact Ideal.comap_isPrime _ _

abbrev CplAt (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] : Type :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)

end UpperTheory.V.AlgebraTools
