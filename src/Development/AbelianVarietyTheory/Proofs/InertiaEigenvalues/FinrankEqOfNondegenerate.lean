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

namespace GlobalTheory.NondegenerateFinrank

theorem finrank_eq_of_nondegenerate {LL : Type} [Field LL] {V V' : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (h1 : ∀ (x : V), (∀ (y : V'), P x y = 0) → x = 0)
    (h2 : ∀ (y : V'), (∀ (x : V), P x y = 0) → y = 0) :
    Module.finrank LL V = Module.finrank LL V' := by
  have i1 : Function.Injective P := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact h1 x (fun y => by simp [hx])
  have i2 : Function.Injective P.flip := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact h2 y (fun x => by
      have := LinearMap.congr_fun hy x
      simpa using this)
  have a := LinearMap.finrank_le_finrank_of_injective i1
  have b := LinearMap.finrank_le_finrank_of_injective i2
  have ea : Module.finrank LL (V' →ₗ[LL] LL) = Module.finrank LL V' := Subspace.dual_finrank_eq
  have eb : Module.finrank LL (V →ₗ[LL] LL) = Module.finrank LL V := Subspace.dual_finrank_eq
  omega

theorem main : ∀ {LL : Type} [inst : Field LL] {V V' : Type} [inst_1 : AddCommGroup V] [inst_2 : Module LL V] [FiniteDimensional LL V] [inst_4 : AddCommGroup V'] [inst_5 : Module LL V'] [FiniteDimensional LL V'] (P : V →ₗ[LL] V' →ₗ[LL] LL), (∀ (x : V), (∀ (y : V'), ((P : V → V' →ₗ[LL] LL) x : V' → LL) y = (0 : LL)) → x = (0 : V)) → (∀ (y : V'), (∀ (x : V), ((P : V → V' →ₗ[LL] LL) x : V' → LL) y = (0 : LL)) → y = (0 : V')) → Module.finrank LL V = Module.finrank LL V' :=
  fun P h1 h2 => finrank_eq_of_nondegenerate P h1 h2

end GlobalTheory.NondegenerateFinrank
