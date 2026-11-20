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
import Mathlib.Topology.Sheaves.Init

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem bilinForm_bijective_of_nondegenerate_mod (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (E : LinearMap.BilinForm ℤ X)
    (h : ∀ (k : ℕ) (a : X), 0 < k → (∀ b, (k : ℤ) ∣ E a b) → ∃ a', a = (k : ℤ) • a') :
    Function.Bijective E := by
  classical
  set b := Module.Free.chooseBasis ℤ X
  have hinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).2 fun a ha => ?_
    refine b.ext_elem fun i => ?_
    obtain ⟨n, hn⟩ : ∃ n, (b.repr a i).natAbs = n := ⟨_, rfl⟩
    obtain ⟨a', ha'⟩ := h (n + 1) a (Nat.succ_pos n) (fun y => by rw [ha]; simp)
    have hdvd : ((n + 1 : ℕ) : ℤ) ∣ b.repr a i := ⟨b.repr a' i, by rw [ha']; simp⟩
    rw [map_zero, Finsupp.zero_apply]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd ?_
    rw [Int.natAbs_natCast, hn]
    exact Nat.lt_succ_self n
  have hrank : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) = 0 := by
    have h1 := rank_quotient_add_rank_of_isDomain (LinearMap.range E)
    rw [← (LinearEquiv.ofInjective E hinj).rank_eq, ← b.toDualEquiv.rank_eq] at h1
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 (Module.rank_lt_aleph0 ℤ X)
    have hq : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) < Cardinal.aleph0 :=
      lt_of_le_of_lt (le_self_add) (h1 ▸ Module.rank_lt_aleph0 ℤ X)
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hq
    rw [hm, hn] at h1
    rw [hm]
    have : m + n = n := by exact_mod_cast h1
    exact_mod_cast (by omega : m = 0)
  refine ⟨hinj, fun f => ?_⟩
  obtain ⟨c, hc0, hcf⟩ := rank_eq_zero_iff.1 hrank (Submodule.Quotient.mk f)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcf
  obtain ⟨x, hx⟩ := hcf
  have hk : 0 < c.natAbs * c.natAbs := Nat.mul_pos (Int.natAbs_pos.2 hc0) (Int.natAbs_pos.2 hc0)
  obtain ⟨a', ha'⟩ := h (c.natAbs * c.natAbs) (c • x) hk (fun y => by
    rw [Int.natAbs_mul_self, map_smul, hx, smul_smul]
    simp)
  refine ⟨a', ?_⟩
  have hEq : E (c • x) = ((c.natAbs * c.natAbs : ℕ) : ℤ) • f := by
    rw [Int.natAbs_mul_self, map_smul, hx, smul_smul]
  rw [ha', map_smul] at hEq
  ext y
  have hy := LinearMap.congr_fun hEq y
  simp only [LinearMap.smul_apply, smul_eq_mul] at hy
  exact mul_left_cancel₀ (by exact_mod_cast hk.ne') hy

end GlobalTheory
