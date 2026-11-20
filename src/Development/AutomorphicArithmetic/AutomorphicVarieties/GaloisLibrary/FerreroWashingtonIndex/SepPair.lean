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
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
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

open UpperTheory.V.FW

private theorem sep_pair (l : ℕ) [Fact l.Prime] (x y : ℤ_[l]) :
    ∀ᶠ n in Filter.atTop, PadicInt.toZModPow n x = PadicInt.toZModPow n y → x = y := by
  by_cases h : x = y
  · exact Filter.Eventually.of_forall fun _ _ => h
  · obtain ⟨m, hm⟩ : ∃ m, PadicInt.toZModPow m x ≠ PadicInt.toZModPow m y := by
      by_contra hc
      push_neg at hc
      exact h (PadicInt.ext_of_toZModPow.mp hc)
    filter_upwards [Filter.eventually_ge_atTop m] with n hn heq
    exfalso
    apply hm
    rw [← PadicInt.cast_toZModPow m n hn x, ← PadicInt.cast_toZModPow m n hn y, heq]

theorem UpperTheory.V.FW.sep :
    ∀ (l : ℕ) [Fact l.Prime] (S : Finset ℤ_[l]), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Set.InjOn (PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) S := by
  intro l _ S
  have h : ∀ᶠ n in Filter.atTop, ∀ p ∈ S ×ˢ S,
      PadicInt.toZModPow n p.1 = PadicInt.toZModPow n p.2 → p.1 = p.2 :=
    (Filter.eventually_all_finset _).mpr fun p _ => sep_pair l p.1 p.2
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨n₀, fun n hn x hx y hy hxy => hn₀ n hn (x, y) (Finset.mk_mem_product hx hy) hxy⟩
