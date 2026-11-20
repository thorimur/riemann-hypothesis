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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace AddCharEqMulShift

private lemma card_le (F K : Type) [Field F] [Fintype F] [Field K] :
    Finite (AddChar F K) ∧ Nat.card (AddChar F K) ≤ Nat.card F := by
  have hli : LinearIndependent K
      (fun ψ : AddChar F K => ((AddChar.toMonoidHomEquiv ψ : Multiplicative F →* K) :
        Multiplicative F → K)) :=
    (linearIndependent_monoidHom (Multiplicative F) K).comp _
      AddChar.toMonoidHomEquiv.injective
  have hfin : Finite (AddChar F K) := hli.finite
  refine ⟨hfin, ?_⟩
  haveI : Fintype (AddChar F K) := Fintype.ofFinite _
  have h := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  simpa [Nat.card_eq_fintype_card] using h

end AddCharEqMulShift

theorem UpperTheory.Reformulated.B.Yde4.main :
    ∀ {F K : Type} [inst : Field F] [Fintype F] [inst_2 : Field K] (ψ₀ ψ : AddChar F K),
      ψ₀ ≠ (1 : AddChar F K) → ∃ (c : F), ψ = ψ₀.mulShift c := by
  intro F K _ _ _ ψ₀ ψ h
  obtain ⟨hfin, hle⟩ := AddCharEqMulShift.card_le F K
  have hinj : Function.Injective ψ₀.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one h)
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hle).2 ψ
  exact ⟨c, hc.symm⟩
