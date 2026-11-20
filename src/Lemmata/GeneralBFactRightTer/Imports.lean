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

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Bl.general_b_fact_right_ter

theorem goal1 {F : Type} [Field F] [NumberField F] {ι : Type} (s : Finset ι)
    (Q : ι → 𝓞 F → Prop) (hQ : ∀ i c r, Q i c → Q i (c * r)) (h : ∀ i ∈ s, ∃ c, c ≠ 0 ∧ Q i c) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i ∈ s, Q i c := by
  classical
  choose! c hc0 hcQ using h
  refine ⟨∏ i ∈ s, c i, Finset.prod_ne_zero_iff.mpr hc0, ?_⟩
  intro i hi
  rw [← Finset.mul_prod_erase s c hi]
  exact hQ i _ _ (hcQ i hi)

end Bl.general_b_fact_right_ter
