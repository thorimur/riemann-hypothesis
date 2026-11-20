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
import Mathlib.RingTheory.SimpleRing.Principal
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
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem fg_of_saturated_ideal_power_into_image :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] (I : Ideal S),
      (∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ I ^ k, IsLocalization.IsInteger S (a • c)) →
        IsLocalization.IsInteger S c) →
      ∀ (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M]
        (N : Submodule S (FractionRing S ⊗[S] M)),
        (∀ z ∈ N, ∃ k : ℕ, ∀ a ∈ I ^ k,
          a • z ∈ LinearMap.range (TensorProduct.mk S (FractionRing S) M 1)) → N.FG := by
  intro S _ _ _ I hsat M _ _ _ N hN
  classical
  set K := FractionRing S
  let V := K ⊗[S] M
  let b := Module.Free.chooseBasis K V
  let ι := Module.Free.ChooseBasisIndex K V
  let T : V →ₗ[S] (ι → K) := (b.equivFun.toLinearMap).restrictScalars S

  let L : Submodule S (ι → K) := LinearMap.range ((Algebra.linearMap S K).compLeft ι)
  have memL : ∀ v : ι → K, (∀ i, IsLocalization.IsInteger S (v i)) → v ∈ L := by
    intro v hv
    choose w hw using hv
    exact ⟨w, funext fun i => hw i⟩
  have memL' : ∀ v ∈ L, ∀ i, IsLocalization.IsInteger S (v i) := by
    rintro v ⟨w, rfl⟩ i
    exact ⟨w i, rfl⟩
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := S) (M := M)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors S)
    (Finset.univ : Finset (Fin n × ι)) (fun p => T (1 ⊗ₜ g p.1) p.2)
  let F : V →ₗ[S] (ι → K) := (d : S) • T
  have hFM : ∀ m : M, F (1 ⊗ₜ m) ∈ L := by
    intro m
    have hle : Submodule.span S (Set.range g) ≤ L.comap (F ∘ₗ TensorProduct.mk S K M 1) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show F (1 ⊗ₜ g j) ∈ L
      apply memL
      intro i
      exact hd (j, i) (Finset.mem_univ _)
    have : m ∈ Submodule.span S (Set.range g) := by rw [hg]; trivial
    exact hle this
  have hFN : ∀ z ∈ N, F z ∈ L := by
    intro z hz
    obtain ⟨k, hk⟩ := hN z hz
    apply memL
    intro i
    apply hsat k
    intro a ha
    obtain ⟨m, hm⟩ := hk a ha
    have h1 := hFM m
    simp only [TensorProduct.mk_apply] at hm
    rw [hm, map_smul] at h1
    simpa using memL' _ h1 i
  have hFinj : Function.Injective F := by
    intro x y hxy
    have hd0 : algebraMap S K (d : S) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have : algebraMap S K (d : S) • b.equivFun x = algebraMap S K (d : S) • b.equivFun y := by
      simpa [F, T, algebraMap_smul] using hxy
    exact b.equivFun.injective (smul_right_injective _ hd0 this)
  have hLfg : L.FG := by
    show (LinearMap.range ((Algebra.linearMap S K).compLeft ι)).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  haveI : IsNoetherian S L := isNoetherian_of_fg_of_noetherian L hLfg
  apply Submodule.fg_of_fg_map_injective F hFinj
  exact Submodule.FG.of_le_of_isNoetherian (T := L) (by
    rintro _ ⟨z, hz, rfl⟩
    exact hFN z hz)

end GlobalTheory
