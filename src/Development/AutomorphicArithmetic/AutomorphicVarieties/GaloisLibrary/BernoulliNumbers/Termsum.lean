import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LSeries.HurwitzZeta
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Finset UpperTheory.V.Bern

private theorem hasSum_hurwitzZeta (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (((n : ℝ) + x : ℝ) : ℂ) ^ (-s)) (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s) := by
  convert HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨h0, h1⟩ hs using 1
  ext1 n
  rw [Complex.cpow_neg, one_div]
  push_cast
  rfl

theorem UpperTheory.V.Bern.b_termsum :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → ∀ s : ℂ, 1 < s.re → ∑' n : ℕ, ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (1 - (x : ℂ)) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s))) = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ)) := by
  intro x hx0 hx1 s hs
  have hA := hasSum_hurwitzZeta x hx0.le hx1 s hs
  have hB := hasSum_hurwitzZeta 1 zero_le_one le_rfl s hs
  have hC : HasSum (fun n : ℕ => ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) (HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hB
    have e1 : (fun n : ℕ => ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) = fun n : ℕ => (((((n + 1 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) := by
      funext n
      congr 1
      push_cast
      ring
    have e2 : ∑ i ∈ range 1, (((((i : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) = 1 := by
      simp
    rw [e1, ← e2]
    exact h
  have hT := (hA.sub hB).sub ((hB.sub hC).mul_left (1 - (x : ℂ)))
  rw [hT.tsum_eq]
  ring
