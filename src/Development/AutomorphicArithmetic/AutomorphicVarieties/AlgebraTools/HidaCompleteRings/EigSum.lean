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
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.exists_eigenvector_fixed_idempotent {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U f : Module.End K V) (hc : Commute U f) (μ : K) :
    ∀ (k : ℕ) (y : V), y ≠ 0 → f y = y → ((U - μ • (1 : Module.End K V)) ^ k) y = 0 →
      ∃ z : V, z ≠ 0 ∧ f z = z ∧ U z = μ • z := by
  intro k
  induction k with
  | zero =>
    intro y hy _ h
    rw [pow_zero, Module.End.one_apply] at h
    exact absurd h hy
  | succ k ih =>
    intro y hy hfy hk
    by_cases hw : (U - μ • (1 : Module.End K V)) y = 0
    · refine ⟨y, hy, hfy, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hw
      exact hw
    · apply ih _ hw
      · have hc' : Commute (U - μ • (1 : Module.End K V)) f :=
          hc.sub_left (Commute.smul_left (Commute.one_left f) μ)
        have := LinearMap.congr_fun hc'.eq y
        rw [Module.End.mul_apply, Module.End.mul_apply, hfy] at this
        exact this.symm
      · rw [← Module.End.mul_apply, ← pow_succ]
        exact hk

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.idempotent_kills_generalized_eigenspace {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U f : Module.End K V) (hf : IsIdempotentElem f) (hc : Commute U f) (μ : K)
    (h : ∀ z : V, z ≠ 0 → f z = z → U z = μ • z → False) (y : V)
    (hy : y ∈ U.maxGenEigenspace μ) : f y = 0 := by
  by_contra hne
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace U μ y).mp hy
  have hc' : Commute ((U - μ • (1 : Module.End K V)) ^ k) f :=
    (hc.sub_left (Commute.smul_left (Commute.one_left f) μ)).pow_left k
  obtain ⟨z, hz, hfz, hUz⟩ := exists_eigenvector_fixed_idempotent U f hc μ k (f y) hne
    (by rw [← Module.End.mul_apply, hf.eq])
    (by rw [← Module.End.mul_apply, hc'.eq, Module.End.mul_apply, hk, map_zero])
  exact h z hz hfz hUz

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigSum :
    ∀ {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (U e : Module.End K V) (S : Set K), IsIdempotentElem e → Commute U e → (∀ μ y, y ≠ 0 → e y = y → U y = μ • y → μ ∈ S) → (∀ μ y, y ≠ 0 → e y = 0 → U y = μ • y → μ ∉ S) → LinearMap.range e = ⨆ μ ∈ S, U.maxGenEigenspace μ := by
  intro K V _ _ _ _ _ U e S he hc h1 h2
  have hE : ∀ μ, Submodule.map e (U.maxGenEigenspace μ) ≤ U.maxGenEigenspace μ := by
    intro μ
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace U μ y).mp hy
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨k, ?_⟩
    have hc' : Commute ((U - μ • (1 : Module.End K V)) ^ k) e :=
      (hc.sub_left (Commute.smul_left (Commute.one_left e) μ)).pow_left k
    rw [← Module.End.mul_apply, hc'.eq, Module.End.mul_apply, hk, map_zero]
  apply le_antisymm
  · rw [LinearMap.range_eq_map, ← Module.End.iSup_maxGenEigenspace_eq_top U, Submodule.map_iSup]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ∈ S
    · exact (hE μ).trans (le_iSup₂_of_le μ hμ le_rfl)
    · rintro _ ⟨y, hy, rfl⟩
      have h0 : e y = 0 :=
        idempotent_kills_generalized_eigenspace U e he hc μ (fun z hz hez hUz => hμ (h1 μ z hz hez hUz)) y hy
      rw [h0]
      exact Submodule.zero_mem _
  · refine iSup₂_le fun μ hμ => ?_
    intro y hy
    have hf : IsIdempotentElem (1 - e) := he.one_sub
    have hc1 : Commute U (1 - e) := (Commute.one_right U).sub_right hc
    have h0 := idempotent_kills_generalized_eigenspace U (1 - e) hf hc1 μ
      (fun z hz hez hUz => h2 μ z hz
        (by rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_self] at hez; exact hez) hUz hμ) y hy
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
    exact ⟨y, h0.symm⟩
