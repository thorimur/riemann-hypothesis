import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem tendsto_cube_mul_derivWeierstrassP (L : PeriodPair) :
    Filter.Tendsto (fun z : ℂ => z ^ 3 * L.derivWeierstrassP z) (𝓝[≠] 0) (𝓝 (-2)) := by
  have hw : ContinuousAt (fun z : ℂ ↦ z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) 0 := by
    have := (L.analyticAt_derivWeierstrassPExcept 0).continuousAt
    fun_prop
  have h1 : Filter.Tendsto (fun z : ℂ ↦ z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) (𝓝[≠] 0)
      (𝓝 (-2)) := by
    have := hw.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  have h := L.derivWeierstrassPExcept_sub 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  rw [← h]
  field_simp

end GlobalTheory.CMModel
