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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.FrobSemisimpleUnique

theorem isNilpotent_zpow_sub_one {R : Type*} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (d : ℤ) : IsNilpotent (((u ^ d : Rˣ) : R) - 1) := by
  have hnat : ∀ n : ℕ, IsNilpotent (((u ^ n : Rˣ) : R) - 1) := by
    intro n
    rw [Units.val_pow_eq_pow_val, ← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    refine Commute.sum_left _ _ _ fun i _ => ?_
    exact ((Commute.refl (u : R)).sub_right (Commute.one_right _)).pow_left i
  obtain ⟨n, rfl | rfl⟩ := d.eq_nat_or_neg
  · rw [zpow_natCast]; exact hnat n
  · rw [zpow_neg, zpow_natCast]
    have h1 := hnat n
    generalize u ^ n = v at h1
    have h2 : ((v⁻¹ : Rˣ) : R) - 1 = -(((v⁻¹ : Rˣ) : R) * ((v : R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [h2]
    refine (Commute.isNilpotent_mul_left ?_ h1).neg
    exact ((Commute.refl v).inv_left.units_val).sub_right (Commute.one_right _)

theorem nilpotent_part {R : Type*} [Ring R] {f s : R} (v : Rˣ) (hv : IsNilpotent ((v : R) - 1))
    (hc : Commute (v : R) f) (hf : f = s * v) : IsNilpotent (f - s) ∧ Commute (f - s) s := by
  have hs : s = f * ((v⁻¹ : Rˣ) : R) := by rw [hf, Units.mul_inv_cancel_right]
  have hvs : Commute (v : R) s := by
    rw [hs]
    exact hc.mul_right (Commute.refl v).inv_right.units_val
  have h1 : f - s = s * ((v : R) - 1) := by rw [hf, mul_sub, mul_one]
  have h2 : Commute s ((v : R) - 1) := hvs.symm.sub_right (Commute.one_right _)
  rw [h1]
  exact ⟨h2.isNilpotent_mul_left hv, (Commute.refl s).mul_left h2.symm⟩

end GlobalTheory.WeilDeligne.FrobSemisimpleUnique
