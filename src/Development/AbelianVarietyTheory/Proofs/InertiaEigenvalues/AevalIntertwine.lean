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

namespace GlobalTheory.AevalIntertwine

theorem aeval_intertwine : ∀ {K M N : Type} [inst : Field K] [inst_1 : AddCommGroup M] [inst_2 : Module K M] [inst_3 : AddCommGroup N] [inst_4 : Module K N] (f : M →ₗ[K] N) (A : Module.End K M) (B : Module.End K N), (∀ (x : M), (f : M → N) ((A : M → M) x) = (B : N → N) ((f : M → N) x)) → ∀ (p : Polynomial K) (x : M), (f : M → N) (((Polynomial.aeval A : Polynomial K → Module.End K M) p : M → M) x) = ((Polynomial.aeval B : Polynomial K → Module.End K N) p : N → N) ((f : M → N) x) := by
  intro K M N _ _ _ _ _ f A B h p
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a x
    simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  · intro p q hp hq x
    simp only [map_add, LinearMap.add_apply, hp, hq]
  · intro n a ih x
    have e : ∀ {V : Type} [AddCommGroup V] [Module K V] (E : Module.End K V) (y : V),
        Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ (n + 1)) y
          = Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n) (E y) := by
      intro V _ _ E y
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [e, e, ih, h]

end GlobalTheory.AevalIntertwine
