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
import Std.Tactic.BVDecide.Normalize.Prop

open Matrix
open scoped Classical

namespace GlobalTheory

theorem pi_prod_rows_orthonormal {K : Type} [Fintype K] [DecidableEq K] {κ : K → Type}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)] [DecidableEq (∀ k, κ k)]
    (A : ∀ k, Matrix (κ k) (κ k) ℂ)
    (hA : ∀ k a b, ∑ y, A k a y * star (A k b y) = if a = b then 1 else 0)
    (T T'' : ∀ k, κ k) :
    ∑ x : ∀ k, κ k, (∏ k, A k (T k) (x k)) * star (∏ k, A k (T'' k) (x k)) =
      if T = T'' then 1 else 0 := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k y => A k (T k) y * star (A k (T'' k) y))]
  rw [Finset.prod_congr rfl (fun k _ => hA k (T k) (T'' k)), Finset.prod_boole]
  by_cases hT : T = T''
  · subst hT; simp
  · rw [if_neg hT, if_neg]
    intro hall
    exact hT (funext fun k => hall k (Finset.mem_univ k))

theorem unitary_tensor_places_positions : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι]
    [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) →
    (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈
      Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by
  intro J ι _ _ _ _ n C hC
  have hC' : ∀ j (a b : ι), ∑ y, C j a y * star (C j b y) = if a = b then 1 else 0 := by
    intro j a b
    have := congrFun (congrFun ((mem_unitaryGroup_iff).1 (hC j)) a) b
    rw [mul_apply, one_apply] at this
    simp only [star_apply] at this
    convert this using 1
  have hD : ∀ j (S S'' : Fin (n j) → ι),
      ∑ y : Fin (n j) → ι, (∏ r, C j (S r) (y r)) * star (∏ r, C j (S'' r) (y r)) =
        if S = S'' then 1 else 0 := fun j =>
    pi_prod_rows_orthonormal (κ := fun _ => ι) (fun _ => C j) (fun _ => hC' j)
  have key := pi_prod_rows_orthonormal (κ := fun j => Fin (n j) → ι)
    (fun j => of fun S S' : Fin (n j) → ι => ∏ r, C j (S r) (S' r))
    (fun j a b => by simpa only [of_apply] using hD j a b)
  rw [mem_unitaryGroup_iff]
  ext T T''
  rw [mul_apply, one_apply]
  simp only [star_apply, of_apply]
  simp only [of_apply] at key
  exact key T T''

end GlobalTheory
