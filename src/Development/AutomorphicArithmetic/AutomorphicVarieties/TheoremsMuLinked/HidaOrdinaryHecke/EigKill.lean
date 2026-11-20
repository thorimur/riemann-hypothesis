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
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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

open IsLocalRing

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.eigKill :
    ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] (φ : Module.End K V) (k : ℕ) (F : V), F ∈ ⨆ μ : K, φ.eigenspace μ → (φ ^ k) F = 0 → φ F = 0 := by
  intro K V _ _ _ φ k F hF hk
  have hdisj := Module.End.eigenspaces_iSupIndep φ 0
  set S := ⨆ (μ : K) (_ : μ ≠ 0), φ.eigenspace μ with hS
  have hinv : ∀ z ∈ S, φ z ∈ S := by
    have hle : S ≤ S.comap φ := by
      refine iSup₂_le fun μ hμ => ?_
      intro v hv
      rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.1 hv]
      exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ (Submodule.smul_mem _ _ hv))
    exact fun z hz => hle hz
  have hinj : ∀ z ∈ S, φ z = 0 → z = 0 := by
    intro z hz h0
    have hz0 : z ∈ φ.eigenspace 0 := by
      rw [Module.End.mem_eigenspace_iff, zero_smul]
      exact h0
    exact Submodule.disjoint_def.1 hdisj z hz0 hz
  have hpow : ∀ n : ℕ, ∀ z ∈ S, (φ ^ n) z = 0 → z = 0 := by
    intro n
    induction n with
    | zero =>
      intro z _ h
      simpa using h
    | succ n ih =>
      intro z hz h
      rw [pow_succ, Module.End.mul_apply] at h
      exact hinj z hz (ih _ (hinv z hz) h)
  rw [iSup_split_single _ (0 : K)] at hF
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hF
  have hy' : φ y = 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul] at hy
    exact hy
  cases k with
  | zero =>
    have h0 : y + z = 0 := by simpa using hk
    rw [h0, map_zero]
  | succ k =>
    have hyk : (φ ^ (k + 1)) y = 0 := by
      rw [pow_succ, Module.End.mul_apply, hy', map_zero]
    rw [map_add, hyk, zero_add] at hk
    rw [map_add, hy', hpow _ z hz hk, map_zero, add_zero]
