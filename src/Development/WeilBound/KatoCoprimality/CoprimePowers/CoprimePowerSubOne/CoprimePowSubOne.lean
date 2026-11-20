import GroundTheory.PAdicHodge.GaloisOnCp
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal

noncomputable section

namespace GaloisFrobeniusFixed

open GroundTheory.PAdicHodge GroundTheory.LocalField

variable (l : ℕ) [Fact l.Prime]

abbrev GQ : Type := PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l

abbrev Fld : Type := IntermediateField ℚ_[l] (PadicAlgCl l)

def chi0 : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (PadicAlgCl l) l).comp
    (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l))

variable {l}

def toBot (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) :
    PadicAlgCl l ≃ₐ[(⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))] PadicAlgCl l :=
  { g.toRingEquiv with
    commutes' := fun x => by
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 x.2
      change g (x : PadicAlgCl l) = (x : PadicAlgCl l)
      rw [← hq, AlgEquiv.commutes] }

def σC (g : GQ l) : ℂ_[l] ≃+* ℂ_[l] := galCp (toBot g)

def χ (g : GQ l) : ℚ_[l] := ((chi0 l g : ℤ_[l]) : ℚ_[l])

def Ine (g : GQ l) : Prop := ∀ y : PadicAlgCl l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1

def FixR (σ : GQ l) (a : ℕ) : Prop :=
  ∀ (ζ : PadicAlgCl l) (n : ℕ), 0 < n → n.Coprime l → ζ ^ n = 1 → σ ζ = ζ ^ (l ^ a)

end GaloisFrobeniusFixed

end
