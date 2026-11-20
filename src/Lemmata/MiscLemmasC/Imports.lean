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

open Finset

namespace Bl.SecondBlockLemmaD

theorem goal1 {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (π : A →+ B) (hπ : Function.Surjective π) (G : B → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * ∑ a, G (π a) = (Fintype.card B : ℂ)⁻¹ * ∑ b, G b := by
  have hfib : ∀ b : B, (univ.filter fun a => π a = b).card = (univ.filter fun a => π a = 0).card :=
    fun b => AddMonoidHom.card_fiber_eq_of_mem_range π (hπ b) (hπ 0)
  set c := (univ.filter fun a => π a = 0).card with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact Finset.card_ne_zero.2 ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, map_zero π⟩⟩
  have hsum : ∑ a, G (π a) = ∑ b, (c : ℂ) * G b := by
    rw [← Finset.sum_fiberwise Finset.univ π (fun a => G (π a))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.1 ha).2]), Finset.sum_const,
      hfib b, nsmul_eq_mul]
  have hcard : Fintype.card A = Fintype.card B * c := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := univ)
      (fun _ _ => Finset.mem_univ _)]
    rw [Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hB : (Fintype.card B : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
  rw [hsum, ← Finset.mul_sum, hcard]
  push_cast
  field_simp

end Bl.SecondBlockLemmaD
