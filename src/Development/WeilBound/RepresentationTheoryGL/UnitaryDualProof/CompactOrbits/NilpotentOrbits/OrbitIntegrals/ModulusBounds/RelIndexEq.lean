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

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

theorem relIndex_eq {k : Type} [Field k] {n : ℕ} (I J : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (GI GJ : Subgroup (GL (Fin n) k)) (hJI : J ≤ I)
    (hGI : ∀ u : GL (Fin n) k, u ∈ GI ↔ u.val - 1 ∈ I)
    (hGJ : ∀ u : GL (Fin n) k, u ∈ GJ ↔ u.val - 1 ∈ J)
    (hsurj : ∀ x ∈ I, ∃ u : GL (Fin n) k, u.val = 1 + x)
    (hmul : ∀ u ∈ GI, ∀ y ∈ J, u.val * y ∈ J) :
    GJ.relIndex GI = J.relIndex I := by
  classical
  have hinv : ∀ x ∈ I, ∃ u : GL (Fin n) k, u ∈ GI ∧ u.val = 1 + x := fun x hx => by
    obtain ⟨u, hu⟩ := hsurj x hx
    refine ⟨u, (hGI u).2 ?_, hu⟩
    rw [hu, add_sub_cancel_left]
    exact hx
  let f : GI → I := fun u => ⟨u.1.val - 1, (hGI u.1).1 u.2⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h : a.1.val - 1 = b.1.val - 1 := congrArg Subtype.val hab
    exact Subtype.ext (Units.ext (sub_left_inj.mp h))
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨u, hu, hux⟩ := hinv x.1 x.2
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    show u.val - 1 = x.1
    rw [hux, add_sub_cancel_left]
  let e : GI ≃ I := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have key : ∀ a b : GI, (QuotientGroup.leftRel (GJ.subgroupOf GI)) a b ↔
      (QuotientAddGroup.leftRel (J.addSubgroupOf I)) (e a) (e b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply, Subgroup.mem_subgroupOf,
      AddSubgroup.mem_addSubgroupOf]
    show ((a.1⁻¹ * b.1 : GL (Fin n) k)) ∈ GJ ↔ -(a.1.val - 1) + (b.1.val - 1) ∈ J
    have h1 : -(a.1.val - 1) + (b.1.val - 1) = b.1.val - a.1.val := by abel
    rw [h1, hGJ, Units.val_mul]
    have ha : a.1⁻¹ ∈ GI := GI.inv_mem a.2
    constructor
    · intro h
      have h2 := hmul a.1 a.2 _ h
      have e2 : a.1.val * ((a.1⁻¹).val * b.1.val - 1) = b.1.val - a.1.val := by
        rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
      rwa [e2] at h2
    · intro h
      have h2 := hmul a.1⁻¹ ha _ h
      have e2 : (a.1⁻¹).val * (b.1.val - a.1.val) = (a.1⁻¹).val * b.1.val - 1 := by
        rw [mul_sub, Units.inv_mul]
      rwa [e2] at h2
  have hc := Nat.card_congr (Quotient.congr e key)
  exact hc

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
