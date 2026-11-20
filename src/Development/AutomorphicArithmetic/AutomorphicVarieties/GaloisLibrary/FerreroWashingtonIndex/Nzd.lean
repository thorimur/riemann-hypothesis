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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open UpperTheory.V.FW

theorem UpperTheory.V.FW.nzd :
    ∀ (k A : Type) [CommRing k] [AddCommGroup A] (a : A) (x : AddMonoidAlgebra k A), (∀ m : ℕ, m • a = 0 → m = 0) → (1 - AddMonoidAlgebra.single a 1) * x = 0 → x = 0 := by
  intro k A _ _ a x ha h
  have hx : AddMonoidAlgebra.single a (1:k) * x = x := by
    rw [sub_mul, one_mul, sub_eq_zero] at h; exact h.symm
  have step : ∀ c, x.coeff (c + a) = x.coeff c := by
    intro c
    conv_lhs => rw [← hx]
    rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, add_comm c a, neg_add_cancel_left]
  have key : ∀ b (n : ℕ), x.coeff (b + n • a) = x.coeff b := by
    intro b n
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, ← add_assoc, step, ih]
  by_contra hne
  obtain ⟨b, hb⟩ : ∃ b, x.coeff b ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (AddMonoidAlgebra.ext (Finsupp.ext fun c => by simp [hc c]))
  have hinj : Function.Injective fun n : ℕ => b + n • a := by
    intro n m hnm
    simp only [add_right_inj] at hnm
    rcases le_total n m with hle | hle
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [add_nsmul, left_eq_add] at hnm
      simp [ha d hnm]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [add_nsmul, add_eq_left] at hnm
      simp [ha d hnm]
  exact Set.infinite_of_injective_forall_mem hinj
    (fun n => show b + n • a ∈ (x.coeff.support : Set A) by simp [key, hb])
    x.coeff.support.finite_toSet
