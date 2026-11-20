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
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

namespace CasPsA

variable {n : ℕ}

theorem entry_conj_single (u v : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) :
    (u * Matrix.single a b (1 : ℂ) * v) i j = u i a * v b j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem conj_single_eq (u v : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    u * Matrix.single a b (1 : ℂ) * v = ∑ c, ∑ d, (u c a * v b d) • Matrix.single c d (1 : ℂ) := by
  ext i j
  rw [entry_conj_single]
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem sum_coef_conj (u v : Matrix (Fin n) (Fin n) ℂ) (huv : u * v = 1) (c d : Fin n) :
    ∑ a, ∑ b, (u c a * v b d) • (u * Matrix.single b a (1 : ℂ) * v) = Matrix.single d c (1 : ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, entry_conj_single]
  have h1 : ∀ x y, ∑ k, u x k * v k y = (1 : Matrix (Fin n) (Fin n) ℂ) x y := fun x y => by
    rw [← huv, Matrix.mul_apply]
  calc ∑ a, ∑ b, u c a * v b d * (u i b * v a j)
      = (∑ a, u c a * v a j) * (∑ b, u i b * v b d) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = Matrix.single d c (1 : ℂ) i j := by
        rw [h1, h1, Matrix.one_apply, Matrix.one_apply, Matrix.single_apply]
        split_ifs <;> simp_all

theorem sum_sum_sum_sum_comm (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum_bilin_conj (B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (u v : Matrix (Fin n) (Fin n) ℂ) (huv : u * v = 1) :
    ∑ a, ∑ b, B (u * Matrix.single a b 1 * v) (u * Matrix.single b a 1 * v) =
      ∑ a, ∑ b, B (Matrix.single a b 1) (Matrix.single b a 1) := by
  calc ∑ a, ∑ b, B (u * Matrix.single a b 1 * v) (u * Matrix.single b a 1 * v)
      = ∑ a, ∑ b, ∑ c, ∑ d, (u c a * v b d) • B (Matrix.single c d 1) (u * Matrix.single b a 1 * v) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [conj_single_eq u v a b]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, (u c a * v b d) • B (Matrix.single c d 1) (u * Matrix.single b a 1 * v) :=
        sum_sum_sum_sum_comm _
    _ = ∑ c, ∑ d, B (Matrix.single c d 1) (Matrix.single d c 1) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [← sum_coef_conj u v huv c d]
        simp only [map_sum, map_smul]

end CasPsA

end ReciprocityTheory.ChartRestriction.DS.S7
