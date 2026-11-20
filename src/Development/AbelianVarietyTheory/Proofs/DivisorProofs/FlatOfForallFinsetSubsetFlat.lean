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

open TensorProduct LinearMap

namespace GlobalTheory

theorem flat_of_forall_finset_subset_flat :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M],
      (∀ s : Finset M, ∃ N : Submodule R M, (↑s : Set M) ⊆ ↑N ∧ Module.Flat R ↥N) →
        Module.Flat R M := by
  intro R M _ _ _ h
  refine Module.Flat.iff_lTensor_injective'.mpr fun I => ?_
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨J, hfg, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype (R := R) (M := ↥I) x
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨N, hsN, hN⟩ := h s
  have hJN : J ≤ N := hs ▸ Submodule.span_le.mpr hsN
  obtain ⟨y', hy'⟩ : ∃ y' : ↥N ⊗[R] ↥I, y' = rTensor (↥I) (Submodule.inclusion hJN) y := ⟨_, rfl⟩
  have hxy : rTensor (↥I) J.subtype y = rTensor (↥I) N.subtype y' := by
    rw [hy', ← rTensor_comp_apply]; rfl
  rw [hxy] at hx ⊢
  have hcomm : lTensor M I.subtype (rTensor (↥I) N.subtype y') =
      rTensor R N.subtype (lTensor (↥N) I.subtype y') := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, lTensor_comp_rTensor, rTensor_comp_lTensor]
  rw [hcomm] at hx
  have hinj1 : Function.Injective (rTensor R N.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R) N.subtype Subtype.val_injective
  have h0 : lTensor (↥N) I.subtype y' = 0 := hinj1 (by rw [hx, map_zero])
  have hinj2 : Function.Injective (lTensor (↥N) I.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := ↥N) I.subtype Subtype.val_injective
  have : y' = 0 := hinj2 (by rw [h0, map_zero])
  rw [this, map_zero]

end GlobalTheory
