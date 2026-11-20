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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.QuotientCardinality

open ValuativeRel

theorem main : ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : ↥(Valuation.integer (ValuativeRel.valuation F))}, Irreducible ϖ → ∀ {a : ℤ} {m : ℕ} {u v : (↥(Valuation.integer (ValuativeRel.valuation F)))ˣ}, (↑ϖ : F) ^ a * (↑(↑u : ↥(Valuation.integer (ValuativeRel.valuation F))) : F) * (↑(↑v : ↥(Valuation.integer (ValuativeRel.valuation F))) : F) = (↑ϖ : F) ^ m → a = (↑m : ℤ) := by
  intro F _ _ _ _ ϖ hϖ a m u v h
  have hint := Valuation.integer.integers (ValuativeRel.valuation F)
  have hu : ValuativeRel.valuation F ((u : (ValuativeRel.valuation F).integer) : F) = 1 :=
    hint.one_of_isUnit u.isUnit
  have hv : ValuativeRel.valuation F ((v : (ValuativeRel.valuation F).integer) : F) = 1 :=
    hint.one_of_isUnit v.isUnit
  have hne : (ϖ : F) ≠ 0 := by
    intro h0
    exact hϖ.ne_zero (Subtype.ext (by simpa using h0))
  have hpos : 0 < ValuativeRel.valuation F (ϖ : F) := by
    rw [pos_iff_ne_zero]
    exact (map_ne_zero (ValuativeRel.valuation F)).mpr hne
  have hne1 : ValuativeRel.valuation F (ϖ : F) ≠ 1 := by
    intro h1
    exact hϖ.not_isUnit ((hint.isUnit_iff_valuation_eq_one (x := ϖ)).mpr h1)
  have h2 := congrArg (ValuativeRel.valuation F) h
  rw [map_mul, map_mul, hu, hv, mul_one, mul_one, map_zpow₀, map_pow, ← zpow_natCast] at h2
  exact zpow_right_injective₀ hpos hne1 h2

end GlobalTheory.QuotientCardinality
