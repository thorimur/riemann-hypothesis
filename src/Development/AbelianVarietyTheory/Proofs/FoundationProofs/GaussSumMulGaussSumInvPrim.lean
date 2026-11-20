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
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

theorem gaussSum_mul_gaussSum_inv_prim {K : Type} [Field K] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter K n} {e : AddChar (ZMod n) K} (hχ : χ.IsPrimitive)
    (he : e.IsPrimitive) : gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = (n : K) := by
  classical
  have h1 : ∀ a b : ZMod n, e (b * a) * e⁻¹ b = e (b * (a - 1)) := by
    intro a b
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc gaussSum χ e * gaussSum χ⁻¹ e⁻¹
      = ∑ b, gaussSum χ (e.mulShift b) * e⁻¹ b := by
        rw [show gaussSum χ⁻¹ e⁻¹ = ∑ b, χ⁻¹ b * e⁻¹ b from rfl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gaussSum_mulShift_of_isPrimitive e hχ]
        ring
    _ = ∑ b, ∑ a, χ a * e (b * (a - 1)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gaussSum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [AddChar.mulShift_apply, mul_assoc, h1]
    _ = ∑ a, χ a * ∑ b, e (b * (a - 1)) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ = ∑ a, χ a * (if a - 1 = 0 then (Fintype.card (ZMod n) : K) else 0) := by
        simp_rw [AddChar.sum_mulShift _ he, Nat.cast_ite, Nat.cast_zero]
    _ = n := by
        simp [sub_eq_zero, ZMod.card]

end GlobalTheory.KummerEisensteinGalois
