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
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
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
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

private theorem sum_antidiagonal_filter_ioo_eq_sum_ioo (k : ℕ) (g : ℕ → ℕ → ℂ) :
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k, g a.1 a.2
      = ∑ i ∈ Finset.Ioo 0 k, g i (k - i) := by
  rw [Finset.sum_filter,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if i ∈ Set.Ioo 0 k then g i j else 0),
    ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioo, Finset.mem_Ioo]
  omega

private theorem aeval_psum_eq_sum_map_pow (s : Multiset ℂ) (n : ℕ) :
    MvPolynomial.aeval (fun x : s => (x : ℂ)) (MvPolynomial.psum s ℂ n) = (s.map (· ^ n)).sum := by
  classical
  rw [MvPolynomial.psum, map_sum]
  simp only [map_pow, MvPolynomial.aeval_X]
  conv_rhs => rw [← Multiset.map_univ_coe s]
  rw [Multiset.map_map]
  rfl

theorem multiset_newton_psum (s : Multiset ℂ) (r : ℕ) (hr : 0 < r) :
    (s.map (· ^ r)).sum = (-1) ^ (r + 1) * (r : ℂ) * s.esymm r
      - ∑ i ∈ Finset.Ioo 0 r, (-1) ^ i * s.esymm i * (s.map (· ^ (r - i))).sum := by
  classical
  have key := congrArg (MvPolynomial.aeval (fun x : s => (x : ℂ)))
    (MvPolynomial.psum_eq_mul_esymm_sub_sum s ℂ r hr)
  simp only [map_sub, map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe,
    aeval_psum_eq_sum_map_pow] at key
  rw [key, sum_antidiagonal_filter_ioo_eq_sum_ioo r (fun i j => (-1) ^ i * s.esymm i * (s.map (· ^ j)).sum)]

end GlobalTheory
