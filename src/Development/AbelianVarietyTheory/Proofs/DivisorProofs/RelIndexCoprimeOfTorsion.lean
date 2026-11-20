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
import Mathlib.GroupTheory.FiniteAbelian.Basic
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
open NumberField IsDedekindDomain

namespace GlobalTheory.FGIndex

theorem relIndex_ne_zero_coprime {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ) (hl : l.Prime)
    (_hAB : A ≤ B) (hB : B.FG) (h : ∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) :
    A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l := by
  haveI : AddGroup.FG B := (AddGroup.fg_iff_addSubgroup_fg B).2 hB
  haveI : AddGroup.FG (B ⧸ A.addSubgroupOf B) :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)
  have hq : ∀ q : B ⧸ A.addSubgroupOf B, ∃ n : ℕ, n.Coprime l ∧ n • q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H b =>
      obtain ⟨n, hn, hnA⟩ := h b b.2
      refine ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      simpa using hnA
  haveI : Finite (B ⧸ A.addSubgroupOf B) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨n, hn, hnq⟩ := hq q
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, Nat.coprime_zero_left] at hn; exact absurd hn hl.one_lt.ne'
      · exact h0
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn0, hnq⟩
  have h0 : A.relIndex B ≠ 0 := by
    rw [AddSubgroup.relIndex, AddSubgroup.index]
    exact Nat.card_pos.ne'
  refine ⟨h0, ?_⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  haveI : Fact l.Prime := ⟨hl⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ A.addSubgroupOf B) l hd
  obtain ⟨n, hn, hnx⟩ := hq x
  have : l ∣ n := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hnx
  exact (Nat.Prime.coprime_iff_not_dvd hl).1 (Nat.coprime_comm.1 hn) this

theorem main : ∀ {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ), l.Prime → A ≤ B → B.FG →
    (∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) → A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l :=
  fun A B l hl hAB hB h => relIndex_ne_zero_coprime A B l hl hAB hB h

end GlobalTheory.FGIndex
