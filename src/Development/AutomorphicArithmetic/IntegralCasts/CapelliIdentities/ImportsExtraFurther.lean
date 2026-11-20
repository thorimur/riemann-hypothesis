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

namespace UpperTheory.Reformulated.B.AddCharacterCount.Helpers

private lemma card_le {C F : Type} [Field C] [Fintype F] [AddCommGroup F] :
    Finite (AddChar F C) ∧ Nat.card (AddChar F C) ≤ Nat.card F := by
  have li : LinearIndependent C (M := Multiplicative F → C)
      ((fun f => f : (Multiplicative F →* C) → Multiplicative F → C) ∘ AddChar.toMonoidHomEquiv) :=
    (linearIndependent_monoidHom (Multiplicative F) C).comp _ AddChar.toMonoidHomEquiv.injective
  have h1 := li.cardinalMk_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have hlt : Cardinal.mk (AddChar F C) < Cardinal.aleph0 :=
    lt_of_le_of_lt h1 Cardinal.natCast_lt_aleph0
  have hfin : Finite (AddChar F C) := Cardinal.lt_aleph0_iff_finite.mp hlt
  refine ⟨hfin, ?_⟩
  have : Nat.card (AddChar F C) ≤ Fintype.card (Multiplicative F) := by
    have h2 := Cardinal.toNat_le_toNat h1 Cardinal.natCast_lt_aleph0
    simpa [Nat.card] using h2
  simpa [Nat.card_eq_fintype_card] using this

end UpperTheory.Reformulated.B.AddCharacterCount.Helpers

open UpperTheory.Reformulated.B.AddCharacterCount.Helpers in
theorem UpperTheory.Reformulated.B.AddCharacterCount.main :
    ∀ {C F : Type} [inst : Field C] [inst_1 : Field F] [Fintype F] [DecidableEq F] (ψ : AddChar F C),
      ψ ≠ (1 : AddChar F C) →
        ∃ (e : F ≃ AddChar F C),
          (∀ (h h' : F), (e : F → AddChar F C) (h + h') = (e : F → AddChar F C) h * (e : F → AddChar F C) h') ∧
            ∀ (h a : F), ((e : F → AddChar F C) h : F → C) a = (ψ : F → C) (h * a) := by
  intro C F _ _ _ _ ψ hψ
  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)
  obtain ⟨hfin, hc⟩ := card_le (C := C) (F := F)
  have hbij : Function.Bijective ψ.mulShift := hinj.bijective_of_nat_card_le hc
  refine ⟨Equiv.ofBijective _ hbij, ?_, ?_⟩
  · intro h h'
    simp [AddChar.mulShift_mul]
  · intro h a
    simp
