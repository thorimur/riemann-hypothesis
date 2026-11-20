import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Polynomial Matrix

private theorem UpperTheory.V.AlgebraTools.perm_four_pow_three_or_four :
    ∀ σ : Equiv.Perm (Fin 4), σ ^ 3 = 1 ∨ σ ^ 4 = 1 := by
  set_option maxRecDepth 100000 in
  decide

theorem UpperTheory.V.AlgebraTools.permChar :
    ∀ (G K : Type) [Group G] [Field K] (π : G →* Equiv.Perm (Fin 4)) (χ : G →* Kˣ), π.ker ≤ χ.ker → 0 < orderOf χ ∧ orderOf χ ≤ 4 := by
  intro G K _ _ π χ hker
  have hχ : ∀ g : G, χ g ^ 3 = 1 ∨ χ g ^ 4 = 1 := fun g => by
    rcases UpperTheory.V.AlgebraTools.perm_four_pow_three_or_four (π g) with h | h
    · left
      have hm : g ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, h]
      have hm' := hker hm
      rwa [MonoidHom.mem_ker, map_pow] at hm'
    · right
      have hm : g ^ 4 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, h]
      have hm' := hker hm
      rwa [MonoidHom.mem_ker, map_pow] at hm'
  have hall : (∀ g : G, χ g ^ 3 = 1) ∨ (∀ g : G, χ g ^ 4 = 1) := by
    by_contra hne
    push_neg at hne
    obtain ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩ := hne
    have h4 : χ g ^ 4 = 1 := (hχ g).resolve_left hg
    have h3 : χ g' ^ 3 = 1 := (hχ g').resolve_right hg'
    rcases hχ (g * g') with h | h
    · rw [map_mul, mul_pow, h3, mul_one] at h
      exact hg h
    · rw [map_mul, mul_pow, h4, one_mul] at h
      exact hg' h
  have key : ∀ k, 0 < k → (∀ g : G, χ g ^ k = 1) → 0 < orderOf χ ∧ orderOf χ ≤ k := by
    intro k hk0 h
    have hp : χ ^ k = 1 := MonoidHom.ext fun g => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact h g
    exact ⟨orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk0, hp⟩),
      orderOf_le_of_pow_eq_one hk0 hp⟩
  rcases hall with h | h
  · obtain ⟨a, b⟩ := key 3 (by norm_num) h
    exact ⟨a, b.trans (by norm_num)⟩
  · exact key 4 (by norm_num) h
