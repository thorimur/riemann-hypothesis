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

theorem UpperTheory.Reformulated.B.AevalIntertwining.aeval_intertwine :
    ∀ {K : Type} [inst : Field K] {M N : Type} [inst_1 : AddCommGroup M]
    [inst_2 : _root_.Module K M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module K N] (φ : M →ₗ[K] N)
    (f : Module.End K M) (f' : Module.End K N),
    (∀ (x : M), (φ : M → N) ((f : M → M) x) = (f' : N → N) ((φ : M → N) x)) →
      ∀ (p : Polynomial K) (x : M),
        (φ : M → N) (((Polynomial.aeval f : Polynomial K → Module.End K M) p : M → M) x) =
          ((Polynomial.aeval f' : Polynomial K → Module.End K N) p : N → N) ((φ : M → N) x) := by
  intro K _ M N _ _ _ _ φ f f' h p
  have hpow : ∀ (n : ℕ) (x : M), φ ((f ^ n) x) = (f' ^ n) (φ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    intro x
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
