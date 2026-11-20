import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.Algebra.Module.Lattice
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertWitt

def stdLat (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  LinearMap.range (LinearMap.pi fun i : Fin n => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i))

theorem mem_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (x : Fin n → E) :
    x ∈ stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact (y i).2
  · intro h
    refine ⟨fun i => ⟨x i, h i⟩, funext fun i => rfl⟩

theorem stdLat_isLattice (E : Type) [Field E] [NumberField E] (n : ℕ) : (stdLat E n).IsLattice E := by
  refine ⟨?_, ?_⟩
  · rw [stdLat, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  · rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i, x i • Pi.single i (1 : E) := by
      ext j; simp [Pi.single_apply]
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine (mem_stdLat _).2 fun j => ?_
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero

end GlobalTheory.InertWitt
