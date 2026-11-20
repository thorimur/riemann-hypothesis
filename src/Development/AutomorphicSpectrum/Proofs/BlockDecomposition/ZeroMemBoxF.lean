import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import GroundTheory.GlobalFields.Adele.Approximation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RedCov.Simple

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def boxF (ρ : ℝ) : Set (AF F) :=
  {a | (∀ w : InfinitePlace F, ‖a.1 w‖ ≤ ρ) ∧ a.2 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}

def boxE (ρ : ℝ) : Set (AF F ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr x k ∈ boxF F ρ}

theorem zero_mem_boxF {ρ : ℝ} (hρ : 0 ≤ ρ) : (0 : AF F) ∈ boxF F ρ :=
  ⟨fun w => by rw [show (0 : AF F).1 w = 0 from rfl, norm_zero]; exact hρ, zero_mem _⟩

theorem zero_mem_boxE {ρ : ℝ} (hρ : 0 ≤ ρ) : (0 : AF F ⊗[F] E) ∈ boxE F E ρ := fun k => by
  simpa using zero_mem_boxF F hρ

end GlobalTheory.CompanionTheory.RedCov.Simple

end
