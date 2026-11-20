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
import Mathlib.RingTheory.WittVector.IsPoly
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

open Polynomial

namespace GlobalTheory.ReesAlgebraMembership

variable {K A : Type*} [CommSemiring K] [Semiring A] [Algebra K A]

def reesAlg (M : ℕ → Submodule K A) [SetLike.GradedMonoid M] : Subalgebra K A[X] where
  carrier := {f | ∀ n, f.coeff n ∈ M n}
  add_mem' := fun {f g} hf hg n => by
    rw [coeff_add]
    exact (M n).add_mem (hf n) (hg n)
  mul_mem' := fun {f g} hf hg n => by
    rw [coeff_mul]
    refine (M n).sum_mem fun c hc => ?_
    have hn : c.1 + c.2 = n := by simpa using hc
    rw [← hn]
    exact SetLike.mul_mem_graded (hf c.1) (hg c.2)
  algebraMap_mem' := fun r n => by
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      rw [Algebra.algebraMap_eq_smul_one]
      exact (M 0).smul_mem r (SetLike.one_mem_graded M)
    · exact (M n).zero_mem

variable (M : ℕ → Submodule K A) [SetLike.GradedMonoid M]

end GlobalTheory.ReesAlgebraMembership
