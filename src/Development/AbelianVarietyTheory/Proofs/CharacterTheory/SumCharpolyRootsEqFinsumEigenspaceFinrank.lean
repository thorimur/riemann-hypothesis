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
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem sum_roots_charpoly_eq_finsum_eigenspace (k : Type) [Field k] [IsAlgClosed k] (V : Type)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (g : Module.End k V) (N : ℕ)
    (hN : (N : k) ≠ 0) (hg : g ^ N = 1) (h : k → ℂ) :
    ((LinearMap.charpoly g).roots.map h).sum =
      ∑ᶠ μ ∈ {μ : k | μ ^ N = 1}, (Module.finrank k (Module.End.eigenspace g μ) : ℂ) * h μ := by
  classical
  have hsep : (X ^ N - C (1 : k) : k[X]).Separable := separable_X_pow_sub_C 1 hN one_ne_zero
  have hss : g.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hg])
  have hdim : ∀ μ, Module.finrank k (Module.End.eigenspace g μ) =
      (LinearMap.charpoly g).roots.count μ := by
    intro μ
    rw [← hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ,
      LinearMap.finrank_maxGenEigenspace_eq, count_roots]
  rw [Finset.sum_multiset_map_count]
  rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := (LinearMap.charpoly g).roots.toFinset)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hdim, nsmul_eq_mul]
  · ext μ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, Finset.mem_coe,
      Multiset.mem_toFinset]
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨?_, h2⟩
      by_contra hc
      apply h2
      rw [hdim, Multiset.count_eq_zero_of_notMem hc]
      simp
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hev : g.HasEigenvalue μ := by
        rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
        exact isRoot_of_mem_roots h1
      have h3 := hev.pow N
      rw [hg] at h3
      obtain ⟨v, hv⟩ := h3.exists_hasEigenvector
      have h4 := hv.apply_eq_smul
      have h5 : (μ ^ N - 1) • v = 0 := by
        rw [sub_smul, ← h4]; simp
      exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hv.2)

end GlobalTheory.CuspGL
