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
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem det_mul_strictLower_eq_one (r : ℕ) (N : Matrix (Fin r) (Fin r) ℂ)
    (h0 : ∀ a c : Fin r, a < c → N a c = 0) (h1 : ∀ a, N a a = 1) :
    (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} =>
      if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0).det = 1 := by
  letI L : LinearOrder {p : Fin r × Fin r // p.2 < p.1} :=
    LinearOrder.lift' (fun p => toLex p.1) (fun p q h => Subtype.ext (toLex.injective h))
  have key := @Matrix.det_of_lowerTriangular {p : Fin r × Fin r // p.2 < p.1} ℂ _ _ _ L
    (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} =>
      if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0) (by
      intro p q hpq
      have hlt : toLex p.1 < toLex q.1 := hpq
      rw [Matrix.of_apply]
      split_ifs with h
      · rcases Prod.Lex.toLex_lt_toLex.1 hlt with h2 | ⟨_, h3⟩
        · exact h0 _ _ h2
        · exact absurd h (ne_of_lt h3)
      · rfl)
  rw [key]
  simp [h1]

end GlobalTheory
