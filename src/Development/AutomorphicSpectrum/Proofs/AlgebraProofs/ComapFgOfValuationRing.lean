import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem comap_fg_of_valuationRing (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]
    (ι κ : Type) [Fintype ι] [Fintype κ] (φ : (ι → R) →ₗ[R] (κ → R)) (W : Submodule R (κ → R))
    (hW : W.FG) : (W.comap φ).FG := by
  obtain ⟨c, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hW
  let ψ : ((ι → R) × (Fin c → R)) →ₗ[R] (κ → R) := φ.coprod (Fintype.linearCombination R w)
  have hflat : Module.Flat R (LinearMap.range ψ) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
  have hfree : Module.Free R (LinearMap.range ψ) := Module.free_of_flat_of_isLocalRing
  have hfp : Module.FinitePresentation R (LinearMap.range ψ) :=
    Module.finitePresentation_of_projective _ _
  have hsurj : Function.Surjective ψ.rangeRestrict := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hker : (LinearMap.ker ψ.rangeRestrict).FG :=
    Module.FinitePresentation.fg_ker _ hsurj
  have heq : W.comap φ = (LinearMap.ker ψ.rangeRestrict).map (LinearMap.fst R (ι → R) (Fin c → R)) := by
    ext l
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_ker, LinearMap.fst_apply]
    constructor
    · intro hl
      rw [← hw, ← Fintype.range_linearCombination] at hl
      obtain ⟨a, ha⟩ := hl
      refine ⟨(l, -a), ?_, rfl⟩
      apply Subtype.ext
      simp [ψ, ha]
    · rintro ⟨⟨l', a⟩, h, rfl⟩
      have h' : φ l' + Fintype.linearCombination R w a = 0 := by
        simpa [ψ] using congrArg Subtype.val h
      have hm : Fintype.linearCombination R w a ∈ W := by
        rw [← hw, ← Fintype.range_linearCombination]
        exact ⟨a, rfl⟩
      rw [eq_neg_of_add_eq_zero_left h']
      exact W.neg_mem hm
  rw [heq]
  exact hker.map _

end GlobalTheory.CompanionTheory.Ar.GR
