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
import Mathlib.RingTheory.Ideal.Height
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

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodEtale

def Hart (A R M : Type) [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ a : A, a ≠ 0 → ∀ m : M,
    (∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : M, algebraMap A R u • m = algebraMap A R a • m') →
    ∃ m' : M, m = algebraMap A R a • m'

def TorsionFreeOver (A R M : Type) [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M]
    [Module R M] : Prop :=
  ∀ a : A, a ≠ 0 → ∀ m : M, algebraMap A R a • m = 0 → m = 0

def EtaleLow (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] C)

end GlobalTheory.GoodEtale

example (k : Type) [Field k] : GlobalTheory.GoodEtale.Hart k k k := fun a ha m _ =>
  ⟨a⁻¹ * m, by simp [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha]⟩

example (A : Type) [CommRing A] : GlobalTheory.GoodEtale.TorsionFreeOver A A Unit := fun _ _ _ _ => rfl
