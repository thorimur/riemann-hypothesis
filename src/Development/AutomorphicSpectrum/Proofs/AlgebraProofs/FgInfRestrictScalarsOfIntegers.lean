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
import Mathlib.Topology.Sheaves.Init
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem fg_inf_restrictScalars_of_integers (C : Type) [Field C] (v : Valuation C NNReal) (O : Type)
    [CommRing O] [Algebra O C] (hv : v.Integers O) (V : Type) [AddCommGroup V] [Module C V]
    [Module O V] [IsScalarTower O C V] (L : Submodule O V) (U : Submodule C V) (hL : L.FG) :
    (L ⊓ U.restrictScalars O).FG := by
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := hinj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  let f : L →ₗ[O] (V ⧸ U) := (U.mkQ.restrictScalars O).comp L.subtype
  haveI : Module.Finite O L := Module.Finite.iff_fg.2 hL
  haveI : Module.Finite O (LinearMap.range f) := inferInstance
  haveI : Module.Flat O (LinearMap.range f) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hx⟩ ⟨⟨a, ha⟩, h⟩
    have h1 : a • x = 0 := congrArg Subtype.val h
    have ha0 : algebraMap O C a ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero ha (hinj (by simpa using h0))
    rw [← algebraMap_smul C a x] at h1
    have : x = 0 := (smul_eq_zero.1 h1).resolve_left ha0
    simp [this]
  haveI : Module.Free O (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  let p : L →ₗ[O] V := L.subtype.comp (LinearMap.id - s.comp f.rangeRestrict)
  have key : L ⊓ U.restrictScalars O = LinearMap.range p := by
    apply le_antisymm
    · rintro x ⟨hxL, hxU⟩
      refine ⟨⟨x, hxL⟩, ?_⟩
      have : f.rangeRestrict ⟨x, hxL⟩ = 0 := by
        apply Subtype.ext
        change U.mkQ x = 0
        exact (Submodule.Quotient.mk_eq_zero U).2 hxU
      simp [p, this]
    · rintro _ ⟨y, rfl⟩
      refine ⟨(y - s (f.rangeRestrict y)).2, ?_⟩
      have h2 : f.rangeRestrict (s (f.rangeRestrict y)) = f.rangeRestrict y :=
        LinearMap.congr_fun hs _
      have h3 : f (y - s (f.rangeRestrict y)) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact (congrArg Subtype.val h2).symm
      exact (Submodule.Quotient.mk_eq_zero U).1 h3
  rw [key]
  exact Module.Finite.iff_fg.1 inferInstance

end GlobalTheory.CompanionTheory.Ar.HT
