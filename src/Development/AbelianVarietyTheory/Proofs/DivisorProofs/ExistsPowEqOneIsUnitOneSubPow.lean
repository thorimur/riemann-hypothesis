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

namespace GlobalTheory

theorem exists_pow_eq_one_isUnit_one_sub_pow (T : Type) [CommRing T] [IsDomain T] (q : ℕ) (hq0 : 0 < q) (hq : IsUnit (q : T))
    (hT : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    ∃ ζ : T, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k) := by
  classical
  haveI : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨x, hx⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 hq0)
  have hprim : IsPrimitiveRoot x q := (Polynomial.isRoot_cyclotomic_iff).1 hx
  refine ⟨x, hprim.pow_eq_one, fun k hk hkq => ?_⟩
  set S := Polynomial.nthRootsFinset q (1 : T) with hS
  have h1S : (1 : T) ∈ S := (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (one_pow _)
  have hprod := Polynomial.X_pow_sub_one_eq_prod hq0 hprim
  rw [← Finset.mul_prod_erase S _ h1S] at hprod
  have hgeom : (Polynomial.X - Polynomial.C (1 : T)) * ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = Polynomial.X ^ q - 1 := by
    rw [Polynomial.C_1]; exact mul_geom_sum _ _
  have hne : (Polynomial.X - Polynomial.C (1 : T)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have hcan : ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = ∏ ζ ∈ S.erase 1, (Polynomial.X - Polynomial.C ζ) :=
    mul_left_cancel₀ hne (hgeom.trans hprod)
  have hev := congrArg (Polynomial.eval (1 : T)) hcan
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_C] at hev
  have hmem : x ^ k ∈ S.erase 1 := by
    refine Finset.mem_erase.2 ⟨hprim.pow_ne_one_of_pos_of_lt hk.ne' hkq, ?_⟩
    exact (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow])
  have hdvd : (1 - x ^ k) ∣ (q : T) := hev ▸ Finset.dvd_prod_of_mem _ hmem
  exact isUnit_of_dvd_unit hdvd hq

end GlobalTheory
