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

namespace GlobalTheory.CMModel

theorem valuation_natCast_eq_one_of_coprime (V : ValuationSubring ℂ) (a b : ℕ)
    (h : Nat.Coprime a b) :
    V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by
  have hint : ∀ z : ℤ, V.valuation (z : ℂ) ≤ 1 := fun z =>
    (V.valuation_le_one_iff _).2 (intCast_mem V z)
  have hnat : ∀ n : ℕ, V.valuation (n : ℂ) ≤ 1 := fun n =>
    (V.valuation_le_one_iff _).2 (natCast_mem V n)
  by_contra hcon
  rw [not_or] at hcon
  have ha : V.valuation (a : ℂ) < 1 := lt_of_le_of_ne (hnat a) hcon.1
  have hb : V.valuation (b : ℂ) < 1 := lt_of_le_of_ne (hnat b) hcon.2
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 h
  have hC : (x : ℂ) * (a : ℂ) + (y : ℂ) * (b : ℂ) = 1 := by exact_mod_cast hxy
  have h1 : V.valuation ((x : ℂ) * (a : ℂ)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint x)) ha
  have h2 : V.valuation ((y : ℂ) * (b : ℂ)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint y)) hb
  have h3 := V.valuation.map_add_lt h1 h2
  rw [hC, map_one] at h3
  exact lt_irrefl _ h3

end GlobalTheory.CMModel
