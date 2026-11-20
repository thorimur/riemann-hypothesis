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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf

namespace GlobalTheory.DownLift

theorem abstract_irreducible_of_highestWeight (V : Type) [AddCommGroup V] [Module ℂ V]
    (U : Submodule ℂ V) (hfin : FiniteDimensional ℂ U) (J : Type) (E : J → Module.End ℂ V)
    (st : J → J) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (Hw : V → Prop)
    (hU : ∀ j, ∀ x ∈ U, E j x ∈ U) (han : ∀ x ∈ U, B x x = 0 → x = 0)
    (hadj : ∀ j x y, B (E j x) y = B x (E (st j) y)) (hst : ∀ j, st (st j) = j)
    (hex : ∀ T : Submodule ℂ V, T ≤ U → T ≠ ⊥ → (∀ j, ∀ x ∈ T, E j x ∈ T) →
      ∃ x ∈ T, x ≠ 0 ∧ Hw x)
    (hprop : ∀ x y, x ∈ U → y ∈ U → Hw x → Hw y → x ≠ 0 → ∃ c : ℂ, y = c • x)
    (S : Submodule ℂ V) (hSU : S ≤ U) (hS : S ≠ ⊥) (hSE : ∀ j, ∀ x ∈ S, E j x ∈ S) :
    S = U := by
  classical
  let P : Submodule ℂ V := U ⊓ ⨅ s : S, LinearMap.ker (B (s : V))
  have hP : ∀ y, y ∈ P ↔ y ∈ U ∧ ∀ s ∈ S, B s y = 0 := by
    intro y
    simp [P, Submodule.mem_iInf]
  have hPbot : P = ⊥ := by
    by_contra hne
    have hPE : ∀ j, ∀ x ∈ P, E j x ∈ P := by
      intro j y hy
      rw [hP] at hy ⊢
      refine ⟨hU j y hy.1, fun s hs => ?_⟩
      have h := hadj (st j) s y
      rw [hst] at h
      rw [← h]
      exact hy.2 _ (hSE _ _ hs)
    obtain ⟨y, hyP, hy0, hyw⟩ := hex P inf_le_left hne hPE
    obtain ⟨x, hxS, hx0, hxw⟩ := hex S hSU hS hSE
    rw [hP] at hyP
    obtain ⟨c, hc⟩ := hprop x y (hSU hxS) hyP.1 hxw hyw hx0
    have hyS : y ∈ S := hc ▸ S.smul_mem c hxS
    exact hy0 (han y hyP.1 (hyP.2 y hyS))
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSU
  let b := Module.finBasis ℂ S
  let φ : U →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    LinearMap.pi fun i => (B (b i : V)).comp U.subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    have hy' : ∀ i, B (b i : V) (y : V) = 0 := fun i => congrFun (LinearMap.mem_ker.mp hy) i
    have hyP : (y : V) ∈ P := by
      rw [hP]
      refine ⟨y.2, fun s hs => ?_⟩
      have h := congrArg (fun z : S => (z : V)) (b.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      rw [← h, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy', smul_zero]
    rw [hPbot, Submodule.mem_bot] at hyP
    rw [Submodule.mem_bot]
    exact Subtype.ext hyP
  have hle := LinearMap.finrank_le_finrank_of_injective hφ
  rw [Module.finrank_fin_fun] at hle
  exact Submodule.eq_of_le_of_finrank_le hSU hle

end GlobalTheory.DownLift
