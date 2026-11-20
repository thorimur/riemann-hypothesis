import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd

namespace Bl.general_b_fact_left_bis_form

theorem goal1 :
  ∀ {O : Type} [inst : CommRing.{0} O] [inst_1 : IsDomain.{0} O] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} O V] [inst_4 : Module.{0, 0} (Formalism.MainNotions.G.KK.{0} O) V]
  [IsScalarTower.{0, 0, 0} O (Formalism.MainNotions.G.KK.{0} O) V] (M : Submodule.{0, 0} O V) (y : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} (Formalism.MainNotions.G.KK.{0} O) (SetLike.coe.{0, 0} M)) y →
    Exists.{1} fun (s : O) ↦ And (Ne.{1} s 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} s y))  := by
  intro O _ _ V _ _ _ _ M y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : (s * t) • (x + z) = t • (s • x) + s • (t • z) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [e]
    exact M.add_mem (M.smul_mem t hsx) (M.smul_mem s htz)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors O) a
    refine ⟨(d : O) * s, mul_ne_zero (nonZeroDivisors.ne_zero d.2) hs, ?_⟩
    have e : ((d : O) * s) • (a • x) = n • (s • x) := by
      rw [mul_comm, mul_smul, ← algebraMap_smul (Formalism.MainNotions.G.KK O) (d : O) (a • x), smul_smul,
        mul_comm (algebraMap O (Formalism.MainNotions.G.KK O) (d : O)) a]
      simp only at hnd
      rw [hnd, algebraMap_smul]
      exact smul_comm s n x
    rw [e]
    exact M.smul_mem n hsx

end Bl.general_b_fact_left_bis_form
