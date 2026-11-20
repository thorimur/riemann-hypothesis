import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Radical.NatInt
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

open IsLocalRing

namespace GlobalTheory

theorem exists_isLocalHom_adicCompletion_extend (O : Type) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V]
    [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V) (hψ : IsLocalHom ψ) :
    ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V,
      IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by
  have h1 : maximalIdeal O ≤ (maximalIdeal V).comap ψ :=
    (IsLocalRing.maximalIdeal_comap ψ).ge
  have hn : ∀ n : ℕ, maximalIdeal O ^ n ≤ (maximalIdeal V ^ n).comap ψ := fun n =>
    (Ideal.pow_right_mono h1 n).trans (Ideal.le_comap_pow ψ n)
  let f : (n : ℕ) → AdicCompletion (maximalIdeal O) O →+* V ⧸ maximalIdeal V ^ n := fun n =>
    (Ideal.quotientMap _ ψ (hn n)).comp (AdicCompletion.evalₐ (maximalIdeal O) n : _ →+* _)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal V) hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective _ _ x
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk,
      Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.eq, ← map_sub]
    apply hn m
    have := c.2 hle
    rw [SModEq.sub_mem] at this
    have h2 := neg_mem this
    simpa using h2
  have hev : ∀ a, IsAdicComplete.liftRingHom (maximalIdeal V) f hf (algebraMap O _ a) = ψ a := by
    intro a
    refine congrFun (IsHausdorff.funext' (maximalIdeal V)
      (f := fun a => IsAdicComplete.liftRingHom (maximalIdeal V) f hf (algebraMap O _ a))
      (g := fun a => ψ a) fun n b => ?_) a
    rw [IsAdicComplete.mk_liftRingHom]
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    exact Ideal.quotientMap_mk
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal V) f hf, ?_, hev⟩
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.comp_apply, hev]
  exact h1 ha

end GlobalTheory
