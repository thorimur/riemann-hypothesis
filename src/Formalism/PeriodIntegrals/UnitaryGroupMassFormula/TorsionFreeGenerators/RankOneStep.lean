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

namespace PI.FGTFG

def ProjStep : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M], Module.Projective R M

def SepStep : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] (m : M),
    m ≠ 0 → ∃ g : M →ₗ[R] R, g m ≠ 0

def CopStep : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I J : Ideal R), I ≠ ⊥ → J ≠ ⊥ →
    ∃ a b : R, b ≠ 0 ∧ Ideal.span {a} * J ⊔ Ideal.span {b} * I = Ideal.span {b}

def SplitStep : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M], 2 ≤ Module.finrank R M →
    ∃ (φ : M →ₗ[R] R) (b : R), b ≠ 0 ∧ LinearMap.range φ = Ideal.span {b}

def RankOneStep : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M], Module.finrank R M = 1 →
    ∃ s : Finset M, s.card ≤ 2 ∧ Submodule.span R (s : Set M) = ⊤

end PI.FGTFG
