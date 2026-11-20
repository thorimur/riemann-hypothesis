import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
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

namespace ReciprocityTheory.MultiplicativeHeights

noncomputable def degreeLeEquivAntidiag (D e : ℕ) :
    {α : Fin D →₀ ℕ // α.degree ≤ e} ≃
      ((Finset.univ : Finset (Fin (D + 1))).finsuppAntidiag e) where
  toFun α := ⟨Finsupp.equivFunOnFinite.symm (Fin.cons (e - α.1.degree) (⇑α.1)), by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    rw [Fin.sum_univ_succ]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero, Fin.cons_succ]
    rw [← Finsupp.degree_eq_sum]
    have := α.2
    omega⟩
  invFun β := ⟨Finsupp.equivFunOnFinite.symm (Fin.tail ⇑β.1), by
    have h := (Finset.mem_finsuppAntidiag.mp β.2).1
    rw [Fin.sum_univ_succ] at h
    rw [Finsupp.degree_eq_sum]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.tail]
    omega⟩
  left_inv α := by
    apply Subtype.ext
    ext i
    simp
  right_inv β := by
    apply Subtype.ext
    ext i
    have h := (Finset.mem_finsuppAntidiag.mp β.2).1
    rw [Fin.sum_univ_succ] at h
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero]
      rw [Finsupp.degree_eq_sum]
      simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.tail]
      omega
    · simp [Fin.tail]

theorem card_degree_le (D e : ℕ) :
    Nat.card {α : Fin D →₀ ℕ // α.degree ≤ e} = (e + D).choose D := by
  rw [Nat.card_congr (degreeLeEquivAntidiag D e), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin,
    show D + 1 + e - 1 = D + e by omega, ← Nat.choose_symm_add, add_comm]

end ReciprocityTheory.MultiplicativeHeights
