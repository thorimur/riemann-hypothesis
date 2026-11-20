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

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

universe u

def GenericNoetherNormalisation.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] (n : ℕ) (q : Ideal (MvPolynomial (Fin (n + 1)) A)),
    q.IsPrime → q ≠ ⊥ → q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥ →
    ∃ a : A, a ≠ 0 ∧ ∃ (z : Fin n → MvPolynomial (Fin (n + 1)) A ⧸ q)
      (s : Finset (MvPolynomial (Fin (n + 1)) A ⧸ q)),
      ∀ d : MvPolynomial (Fin (n + 1)) A ⧸ q, ∃ (k : ℕ) (c : MvPolynomial (Fin (n + 1)) A ⧸ q → MvPolynomial (Fin n) A),
        a ^ k • d = ∑ t ∈ s, aeval z (c t) * t

end GroundTheory.Heights₂.Heights
