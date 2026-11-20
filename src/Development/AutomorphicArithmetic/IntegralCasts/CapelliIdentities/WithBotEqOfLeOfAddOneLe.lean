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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf

theorem UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le :
    ∀ {x : WithBot ℕ∞} {c : ℕ},
      (↑c : WithBot ℕ∞) ≤ x → x + (1 : WithBot ℕ∞) ≤ (↑(c + (1 : ℕ)) : WithBot ℕ∞) → x = (↑c : WithBot ℕ∞) := by
  intro x c h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact le_antisymm bot_le h1
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞) := by exact_mod_cast h2
      rw [top_add, top_le_iff] at h3
      exact ENat.coe_ne_top _ h3
    | coe n =>
      have h3 : c ≤ n := by exact_mod_cast h1
      have h4 : n + 1 ≤ c + 1 := by exact_mod_cast h2
      have h5 : n = c := by omega
      subst h5
      rfl
