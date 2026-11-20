import Formalism.HermitianLattices.DefsCS
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

theorem isomOfTrace : IsomOfTrace := by
  intro K V _ _ _ _ _ h g hg
  show ∀ x y, h (g x) (g y) = h x y
  intro x y
  by_contra hne
  have hd : h (g x) (g y) - h x y ≠ 0 := sub_ne_zero.mpr hne
  have key := hg x ((h (g x) (g y) - h x y)⁻¹ • y)
  simp only [map_smul, smul_eq_mul] at key
  have h0 : Algebra.trace ℚ K ((h (g x) (g y) - h x y)⁻¹ * (h (g x) (g y) - h x y)) = 0 := by
    rw [mul_sub, map_sub, key, sub_self]
  rw [inv_mul_cancel₀ hd] at h0
  have h1 : Algebra.trace ℚ K (1 : K) = (Module.finrank ℚ K : ℚ) := by
    rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  rw [h1] at h0
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  exact absurd h0 (by exact_mod_cast hpos.ne')

end Formalism.HermitianLatticesTheory
