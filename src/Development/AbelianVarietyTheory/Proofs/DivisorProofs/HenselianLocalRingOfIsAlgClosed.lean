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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

set_option autoImplicit false

open Polynomial

namespace GlobalTheory.GroupBplus

theorem henselianLocalRing_of_isAlgClosed (S K : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [IsIntegrallyClosed S]
    [Field K] [IsAlgClosed K] [Algebra S K] [IsFractionRing S K] : HenselianLocalRing S where
  is_henselian f hf a₀ h₁ _ := by
    classical
    have hinj : Function.Injective (algebraMap S K) := IsFractionRing.injective S K
    set g := f.map (algebraMap S K) with hgdef
    have hg : g.Monic := hf.map _
    have hint : ∀ α ∈ g.roots, ∃ y : S, algebraMap S K y = α := fun α hα =>
      IsIntegrallyClosed.isIntegral_iff.1 ⟨f, hf, by
        rw [← Polynomial.eval_map]
        exact (Polynomial.mem_roots hg.ne_zero).1 hα⟩
    choose y hy using hint
    set s : Multiset S := g.roots.pmap y fun _ h => h
    have hs : s.map (algebraMap S K) = g.roots := by
      rw [Multiset.map_pmap, Multiset.pmap_congr (q := fun _ => True) (g := fun a _ => a) (H₂ := fun _ _ => trivial) _ (fun a ha _ _ => hy a ha),
        Multiset.pmap_eq_map, Multiset.map_id']
    have hf' : f = (s.map fun a => X - C a).prod := by
      apply Polynomial.map_injective _ hinj
      rw [Polynomial.map_multiset_prod, Multiset.map_map]
      have e := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hg IsAlgClosed.card_roots_eq_natDegree
      rw [← hs, Multiset.map_map] at e
      rw [← hgdef, ← e]
      congr 1
      exact Multiset.map_congr rfl fun a _ => by simp
    have hev : f.eval a₀ = (s.map fun a => a₀ - a).prod := by
      conv_lhs => rw [hf']
      rw [Polynomial.eval_multiset_prod, Multiset.map_map]
      exact congrArg _ (Multiset.map_congr rfl fun a _ => by simp)
    rw [hev] at h₁
    obtain ⟨c, hc, hcm⟩ := ((IsLocalRing.maximalIdeal.isMaximal S).isPrime.multiset_prod_mem_iff_exists_mem _).1 h₁
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hc
    refine ⟨a, ?_, ?_⟩
    · show f.eval a = 0
      rw [hf', Polynomial.eval_multiset_prod, Multiset.map_map]
      exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by simp⟩)
    · rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 hcm

theorem henselianLocalRing_atPrime (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [IsAlgClosed K]
    [Algebra A K] [IsFractionRing A K] (q : Ideal A) [q.IsPrime] : HenselianLocalRing (Localization.AtPrime q) := by
  letI : Algebra (Localization.AtPrime q) K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ K q.primeCompl (nonZeroDivisors A) q.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower A (Localization.AtPrime q) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ K q.primeCompl (nonZeroDivisors A)
      q.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing (Localization.AtPrime q) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl _ K
  haveI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  exact henselianLocalRing_of_isAlgClosed _ K

end GlobalTheory.GroupBplus
