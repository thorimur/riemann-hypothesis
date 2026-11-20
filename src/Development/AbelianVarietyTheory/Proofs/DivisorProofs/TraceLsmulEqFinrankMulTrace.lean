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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem trace_lsmul_free_eq_finrank_mul_trace (R Λ M : Type) [CommRing R] [Nontrivial R] [CommRing Λ] [Nontrivial Λ] [Algebra R Λ] [Module.Free R Λ] [Module.Finite R Λ] [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower R Λ M] [Module.Free Λ M] [Module.Finite Λ M] (a : Λ) :
    LinearMap.trace R M (Algebra.lsmul R R M a) = (Module.finrank Λ M : R) * Algebra.trace R Λ a := by
  classical
  let b := Module.Free.chooseBasis R Λ
  let e := Module.Free.chooseBasis Λ M
  rw [LinearMap.trace_eq_matrix_trace R (b.smulTower e), Algebra.trace_eq_matrix_trace b,
    Module.finrank_eq_card_chooseBasisIndex]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, LinearMap.toMatrix_apply,
    Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, Algebra.leftMulMatrix_eq_repr_mul]
  have h : ∀ i k, (b.repr ((e.repr (((Algebra.lsmul R R M) a) (b i • e k))) k)) i = (b.repr (a * b i)) i := by
    intro i k
    show (b.repr ((e.repr (a • (b i • e k))) k)) i = _
    rw [smul_smul, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  simp only [h]
  rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory
