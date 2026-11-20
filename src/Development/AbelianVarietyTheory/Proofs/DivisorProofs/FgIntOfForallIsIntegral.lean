import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Topology.Sheaves.Presheaf

open NumberField

namespace GlobalTheory

theorem fg_int_of_forall_isIntegral (K' : Type) [Field K'] [NumberField K']
    (M : Submodule ℤ K') (hM : ∀ y ∈ M, IsIntegral ℤ y) : M.FG := by
  let f : 𝓞 K' →ₗ[ℤ] K' := (algebraMap (𝓞 K') K').toIntAlgHom.toLinearMap
  have hle : M ≤ LinearMap.range f := fun y hy => ⟨⟨y, hM y hy⟩, rfl⟩
  have hfg : (M.comap f).FG := IsNoetherian.noetherian _
  have hmap := hfg.map f
  rwa [Submodule.map_comap_eq, inf_eq_right.mpr hle] at hmap

theorem fg_of_integral_functionals (K : Type) [Field K] [NumberField K] (C : Type)
    [AddCommGroup C] [Module K C] [FiniteDimensional K C] [Module (𝓞 K) C]
    [IsScalarTower (𝓞 K) K C] (L : Submodule (𝓞 K) C)
    (h : ∀ x : C, x ≠ 0 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K')
      (φ : C →ₗ[K] K'), φ x ≠ 0 ∧ ∀ y ∈ L, IsIntegral ℤ (φ y)) : L.FG := by
  apply Submodule.FG.of_restrictScalars ℤ
  suffices H : ∀ W : Submodule K C, (L.restrictScalars ℤ ⊓ W.restrictScalars ℤ).FG by
    simpa using H ⊤
  intro W
  induction W using WellFoundedLT.induction with
  | _ W ih =>
    by_cases hW : W = ⊥
    · subst hW
      have hbot : L.restrictScalars ℤ ⊓ (⊥ : Submodule K C).restrictScalars ℤ = ⊥ := by
        ext y
        simp
      rw [hbot]
      exact Submodule.fg_bot
    · obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      obtain ⟨K', _, _, _, φ, hφx, hφL⟩ := h x hx0
      let f : C →ₗ[ℤ] K' := φ.toAddMonoidHom.toIntLinearMap
      have hlt : W ⊓ LinearMap.ker φ < W := by
        refine lt_of_le_of_ne inf_le_left fun heq => hφx ?_
        have hx : x ∈ W ⊓ LinearMap.ker φ := by rw [heq]; exact hxW
        exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx).2
      apply Submodule.fg_of_fg_map_of_fg_inf_ker f
      · apply fg_int_of_forall_isIntegral K'
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
        exact hφL y (Submodule.mem_inf.mp hy).1
      · have heq : L.restrictScalars ℤ ⊓ W.restrictScalars ℤ ⊓ LinearMap.ker f
            = L.restrictScalars ℤ ⊓ (W ⊓ LinearMap.ker φ).restrictScalars ℤ := by
          ext y
          simp [f, and_assoc]
          exact fun _ _ => Iff.rfl
        rw [heq]
        exact ih _ hlt

end GlobalTheory
