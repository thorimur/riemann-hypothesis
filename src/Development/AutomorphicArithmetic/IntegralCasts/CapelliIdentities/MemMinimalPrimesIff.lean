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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

theorem UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] {z : A},
      z ≠ (0 : A) → ∀ (W : Ideal A), W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = (1 : ℕ∞) ∧ z ∈ W := by
  intro A _ _ _ z hz
  have key : ∀ P : Ideal A, P.IsPrime → z ∈ P → (1 : ℕ∞) ≤ P.height := by
    intro P hP hzP
    have hlt : (⊥ : Ideal A) < P := by
      refine bot_lt_iff_ne_bot.mpr fun h => hz ?_
      rw [h] at hzP
      exact Ideal.mem_bot.mp hzP
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    exact le_trans le_add_self this
  intro W
  constructor
  · intro hW
    have hP : W.IsPrime := hW.1.1
    have hzW : z ∈ W := hW.1.2 (Ideal.mem_span_singleton_self z)
    exact ⟨hP, le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hW) (key W hP hzW), hzW⟩
  · rintro ⟨hP, hh, hzW⟩
    obtain ⟨P, hPm, hPW⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem W).mpr hzW)
    have hP' : P.IsPrime := hPm.1.1
    have hzP : z ∈ P := hPm.1.2 (Ideal.mem_span_singleton_self z)
    rcases hPW.eq_or_lt with h | h
    · exact h ▸ hPm
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := by
        calc (1 : ℕ∞) + 1 ≤ P.height + 1 := by gcongr; exact key P hP' hzP
          _ ≤ W.height := h1
          _ = 1 := hh
      exact absurd h2 (by decide)
