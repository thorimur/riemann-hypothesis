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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

theorem UpperTheory.exists_residue_map_padicAlgCl_integers :
    ∀ (l : ℕ) [Fact l.Prime], ∃ (k : Type) (_ : Field k) (_ : CharP k l) (A : Subring (PadicAlgCl l)) (red : A →+* k), (∀ x : PadicAlgCl l, x ∈ A ↔ ‖x‖ ≤ 1) ∧ ∀ x : A, red x = 0 ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  intro l _
  have hna : ∀ x y : PadicAlgCl l, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := fun x y =>
    IsUltrametricDist.norm_add_le_max x y
  let A : Subring (PadicAlgCl l) :=
    { carrier := {x | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, norm_mul] at *
        exact mul_le_one₀ ha (norm_nonneg _) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => (hna a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha }
  have hA : ∀ x : PadicAlgCl l, x ∈ A ↔ ‖x‖ ≤ 1 := fun x => Iff.rfl
  let I : Ideal A :=
    { carrier := {x | ‖(x : PadicAlgCl l)‖ < 1}
      add_mem' := fun {a b} ha hb => lt_of_le_of_lt (hna _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        show ‖((c * x : A) : PadicAlgCl l)‖ < 1
        rw [Subring.coe_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) c.2) hx }
  have hI : ∀ x : A, x ∈ I ↔ ‖(x : PadicAlgCl l)‖ < 1 := fun x => Iff.rfl
  have hmax : I.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨by simp [hI], fun J x hIJ hx hxJ => ?_⟩
    rw [hI, not_lt] at hx
    have h1 : ‖(x : PadicAlgCl l)‖ = 1 := le_antisymm x.2 hx
    have hx0 : (x : PadicAlgCl l) ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : PadicAlgCl l)⁻¹ ∈ A := by
      rw [hA, norm_inv, h1, inv_one]
    have : (⟨_, hinv⟩ : A) * x = 1 := Subtype.ext (inv_mul_cancel₀ hx0)
    rw [← this]
    exact J.mul_mem_left _ hxJ
  haveI := hmax
  have hl : ‖((l : A) : PadicAlgCl l)‖ < 1 := by
    have h := congrArg NNReal.toReal (PadicAlgCl.valuation_p l)
    rw [PadicAlgCl.valuation_coe] at h
    push_cast
    rw [h]
    have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp only [one_div, NNReal.coe_inv, NNReal.coe_natCast]
    exact inv_lt_one_of_one_lt₀ hl1
  refine ⟨A ⧸ I, Ideal.Quotient.field I, ?_, A, Ideal.Quotient.mk I, hA, fun x => ?_⟩
  · rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hl
  · rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hI x
