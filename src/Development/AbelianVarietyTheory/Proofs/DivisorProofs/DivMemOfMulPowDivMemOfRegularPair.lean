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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem div_mem_of_mul_pow_div_mem_of_regularPair (K : Type) [Field K] (O : Subring K) (s t : K)
    (ht : t ∈ O) (h : ∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) (N : ℕ) :
    ∀ g ∈ O, g * t ^ N / s ∈ O → g / s ∈ O := by
  induction N with
  | zero => intro g _ hg; simpa using hg
  | succ N ih =>
    intro g hg hgN
    apply ih g hg
    apply h _ (O.mul_mem hg (O.pow_mem ht N))
    rwa [mul_assoc, ← pow_succ]

theorem regularPair_pow : ∀ (K : Type) [Field K] (O : Subring K) (s t : K), s ∈ O → t ∈ O → s ≠ 0 → (∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) → ∀ (m N : ℕ), ∀ g ∈ O, g * t ^ N / s ^ m ∈ O → g / s ^ m ∈ O := by
  intro K _ O s t hs ht hs0 h m N
  induction m with
  | zero => intro g hg _; simpa using hg
  | succ m ih =>
    intro g hg hgN
    have h1 : g * t ^ N / s ∈ O := by
      have h2 := O.mul_mem hgN (O.pow_mem hs m)
      have e : g * t ^ N / s ^ (m + 1) * s ^ m = g * t ^ N / s := by
        field_simp
        ring
      rwa [e] at h2
    have h3 := div_mem_of_mul_pow_div_mem_of_regularPair K O s t ht h N g hg h1
    have e1 : g / s * t ^ N / s ^ m = g * t ^ N / s ^ (m + 1) := by
      field_simp
      ring
    have e2 : g / s / s ^ m = g / s ^ (m + 1) := by
      field_simp
      ring
    rw [← e2]
    exact ih _ h3 (by rwa [e1])

end GlobalTheory
