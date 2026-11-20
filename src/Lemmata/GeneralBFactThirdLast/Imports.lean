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

namespace Bl.general_b_fact_third_last

theorem goal1 :
  ∀ {a : WithBot.{0} ENat} {n : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} a 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} n 1)) → Eq.{1} a (Nat.cast.{0} n) := by
  intro a n h
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.bot_add, ← WithBot.coe_natCast] at h
    exact WithBot.bot_ne_coe h
  | coe e =>
    have h1 : ((e + 1 : ENat) : WithBot ENat) = (((n : ENat) + 1 : ENat) : WithBot ENat) := by
      rw [WithBot.coe_add, WithBot.coe_one, WithBot.coe_add, WithBot.coe_one, WithBot.coe_natCast, h]
      push_cast
      rfl
    have h2 : e + 1 = (n : ENat) + 1 := WithBot.coe_injective h1
    have h3 : e = (n : ENat) := ENat.add_left_injective_of_ne_top ENat.one_ne_top h2
    rw [h3, WithBot.coe_natCast]

end Bl.general_b_fact_third_last
