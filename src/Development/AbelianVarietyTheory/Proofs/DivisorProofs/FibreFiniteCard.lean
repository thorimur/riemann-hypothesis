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

namespace GlobalTheory.FibreEquivalence

noncomputable def fibreEquiv {H : Type} [Group H] (D C : Subgroup H) (h : D ≤ C) (z : H ⧸ C) :
    { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } ≃ C ⧸ D.subgroupOf C :=
  have key : ∀ y : H ⧸ D,
      (Subgroup.quotientEquivProdOfLE h y).1 = Subgroup.quotientMapOfLE h y := by
    intro y
    induction y using QuotientGroup.induction_on
    rfl
  { toFun := fun y => (Subgroup.quotientEquivProdOfLE h y.1).2
    invFun := fun b => ⟨(Subgroup.quotientEquivProdOfLE h).symm (z, b), by
      rw [← key, Equiv.apply_symm_apply]⟩
    left_inv := fun y => by
      apply Subtype.ext
      change (Subgroup.quotientEquivProdOfLE h).symm
        (z, (Subgroup.quotientEquivProdOfLE h y.1).2) = y.1
      rw [Equiv.symm_apply_eq]
      exact Prod.ext (by rw [key]; exact y.2.symm) rfl
    right_inv := fun b => by
      change (Subgroup.quotientEquivProdOfLE h
        ((Subgroup.quotientEquivProdOfLE h).symm (z, b))).2 = b
      rw [Equiv.apply_symm_apply] }

theorem fibre_finite_card : ∀ {H : Type} [inst : Group H] (D C : Subgroup H) (h : D ≤ C), Subgroup.relIndex D C ≠ (0 : ℕ) → ∀ (z : H ⧸ C), Finite { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } ∧ Nat.card { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } = Subgroup.relIndex D C := by
  intro H _ D C h hD z
  have hcard : Nat.card { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } = Subgroup.relIndex D C := by
    rw [Nat.card_congr (fibreEquiv D C h z)]
    rfl
  exact ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact hD), hcard⟩

end GlobalTheory.FibreEquivalence
