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

theorem UpperTheory.exists_good_without_bad :
    ∀ {P : Type} [DecidableEq P] (Good : Finset P → Prop) (bad : P → Prop), (∀ (S : Finset P) (w : P), Good S → w ∈ S → bad w → Good (S.erase w)) → ∀ S : Finset P, Good S → ∃ T : Finset P, Good T ∧ ∀ w ∈ T, ¬ bad w := by
  intro P _ Good bad h S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    by_cases hb : ∃ w ∈ S, bad w
    · obtain ⟨w, hw, hbw⟩ := hb
      exact ih (S.erase w) (Finset.erase_ssubset hw) (h S w hS hw hbw)
    · exact ⟨S, hS, fun w hw hbw => hb ⟨w, hw, hbw⟩⟩
