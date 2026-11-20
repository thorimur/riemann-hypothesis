import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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

open Matrix

noncomputable section

namespace PositivityTheory.KB.HeightDistance

def nsq {N : ℕ} (v : Fin N → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

def dist1 {ι : Type} [Fintype ι] {N : ℕ} (A : ι → Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (1 + ∑ w, ∑ i, ∑ j, ‖A w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) ^ 2

theorem nsq_nonneg {N : ℕ} (v : Fin N → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun i _ => by positivity

theorem one_le_dist1 {ι : Type} [Fintype ι] {N : ℕ} (A : ι → Matrix (Fin N) (Fin N) ℂ) :
    1 ≤ dist1 A := by
  unfold dist1
  have h0 : 0 ≤ ∑ w, ∑ i, ∑ j, ‖A w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ :=
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  nlinarith

end PositivityTheory.KB.HeightDistance
