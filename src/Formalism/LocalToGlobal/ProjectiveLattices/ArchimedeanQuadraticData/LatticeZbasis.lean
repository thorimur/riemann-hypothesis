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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix

theorem lattice_zbasis {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hfg : L.FG) (hspan : Submodule.span K (L : Set (Fin r → K)) = ⊤) :
    ∃ e : Fin (Module.finrank ℚ K * r) → (Fin r → K), (∀ j, e j ∈ L) ∧ LinearIndependent ℚ e ∧
      ∀ v ∈ L, ∃ n : Fin (Module.finrank ℚ K * r) → ℤ, v = ∑ j, (n j : ℚ) • e j := by
  classical
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set b := Module.Free.chooseBasis ℤ L
  set f : Module.Free.ChooseBasisIndex ℤ L → (Fin r → K) := fun j => (b j : Fin r → K) with hf
  have hfZ : LinearIndependent ℤ f :=
    b.linearIndependent.map' (L.subtype.restrictScalars ℤ) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hfQ : LinearIndependent ℚ f := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hfZ
  have hrep : ∀ v ∈ L, ∃ c : Module.Free.ChooseBasisIndex ℤ L → ℤ, v = ∑ j, (c j : ℚ) • f j := by
    intro v hv
    refine ⟨fun j => b.repr ⟨v, hv⟩ j, ?_⟩
    have h' := congrArg (fun z : L => (z : Fin r → K)) (b.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    conv_lhs => rw [← h']
    exact Finset.sum_congr rfl fun j _ => (Int.cast_smul_eq_zsmul ℚ _ _).symm
  have hS : ∀ v ∈ L, v ∈ Submodule.span ℚ (Set.range f) := by
    intro v hv
    obtain ⟨c, hc⟩ := hrep v hv
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hKL : ∀ v ∈ L, ∀ k : K, k • v ∈ Submodule.span ℚ (Set.range f) := by
    intro v hv k
    have halg : IsAlgebraic ℤ k :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
    obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
    have hmem : ((⟨y • k, hyi⟩ : 𝓞 K)) • v ∈ L := L.smul_mem _ hv
    have hyK : (y : K) ≠ 0 := by exact_mod_cast hy0
    have heq : k • v = ((y : ℚ)⁻¹) • ((⟨y • k, hyi⟩ : 𝓞 K) • v) := by
      rw [algebra_compatible_smul K ((y : ℚ)⁻¹), algebra_compatible_smul K (⟨y • k, hyi⟩ : 𝓞 K), smul_smul]
      congr 1
      simp only [map_inv₀, map_intCast, zsmul_eq_mul]
      show k = (y : K)⁻¹ * ((y : K) * k)
      field_simp
    rw [heq]
    exact Submodule.smul_mem _ _ (hS _ hmem)
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range f) := by
    intro x _
    have hx : x ∈ Submodule.span K (L : Set (Fin r → K)) := hspan ▸ Submodule.mem_top
    have key : ∀ z ∈ Submodule.span K (L : Set (Fin r → K)), ∀ k : K, k • z ∈ Submodule.span ℚ (Set.range f) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem v hv => exact hKL v hv
      | zero => intro k; rw [smul_zero]; exact Submodule.zero_mem _
      | add a c _ _ ha hc => intro k; rw [smul_add]; exact Submodule.add_mem _ (ha k) (hc k)
      | smul c a _ ha => intro k; rw [smul_smul]; exact ha (k * c)
    simpa using key x hx 1
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℚ K * r := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.mk hfQ htop), Module.finrank_pi_fintype]
    simp [mul_comm]
  let eqv := Fintype.equivFinOfCardEq hcard
  refine ⟨f ∘ eqv.symm, fun j => (b (eqv.symm j)).2, hfQ.comp _ eqv.symm.injective, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := hrep v hv
  refine ⟨c ∘ eqv.symm, ?_⟩
  rw [hc]
  exact (Fintype.sum_equiv eqv.symm _ _ (fun j => rfl)).symm

end Formalism.L2.Pj.FundamentalDomainD5
