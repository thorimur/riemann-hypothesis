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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

universe u_1 u_2

namespace GlobalTheory.LengthDualFunctional

open Module

theorem exists_dual_ne_zero_comp_eq_zero {R : Type u_1} [CommRing R] [IsDomain R]
    {M : Type u_2} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (h : LinearMap.det f = 0) :
    ∃ φ : Module.Dual R M, φ ≠ 0 ∧ φ ∘ₗ f = 0 := by
  have hd : LinearMap.det f.dualMap = 0 := by
    rw [LinearMap.det_dualMap]; exact h
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.bot_lt_ker_of_det_eq_zero hd).ne'
  exact ⟨φ, hφ0, by simpa [LinearMap.dualMap_apply'] using hφ⟩

theorem length_self_eq_top (R : Type u_1) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Module.length R R = ⊤ := by
  by_contra hne
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨_, hA⟩ := hne
  haveI : IsArtinianRing R := hA
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem main : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R] {M : Type u_2} [inst_3 : AddCommGroup M] [inst_4 : Module R M] [Module.Free R M] [Module.Finite R M] {f : M →ₗ[R] M}, (LinearMap.det : (M →ₗ[R] M) → R) f = (0 : R) → Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  intro R _ _ _ M _ _ _ _ f h
  obtain ⟨φ, hφ0, hφ⟩ := exists_dual_ne_zero_comp_eq_zero h
  obtain ⟨m, hm⟩ : ∃ m, φ m ≠ 0 := by
    by_contra hc; push_neg at hc; exact hφ0 (LinearMap.ext hc)
  have hle : LinearMap.range f ≤ LinearMap.ker φ := by
    rintro _ ⟨x, rfl⟩
    simpa using congrArg (fun g => g x) hφ
  let ψ := (LinearMap.range f).liftQ φ hle
  let g : R →ₗ[R] M ⧸ LinearMap.range f := LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk m)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have := congrArg ψ hr
    simp [g, ψ] at this
    tauto
  have := Module.length_le_of_injective g hg
  rw [length_self_eq_top] at this
  exact top_le_iff.mp this

end GlobalTheory.LengthDualFunctional
