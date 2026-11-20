import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.LinearAlgebra.Matrix.Hermitian
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

namespace Formalism.NuclearRankWeightBounds.D

open Finset

noncomputable def lead {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) : ℂ :=
  if hi : i ≤ N then (A.submatrix (Fin.castLE hi) (Fin.castLE hi)).det else 1

noncomputable def hs {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.sqrt (∑ a, ∑ b, ‖Y a b‖ ^ 2)

def q0 {N : ℕ} (ep : Fin N → Bool) : ℕ :=
  min (univ.filter fun a => ep a = true).card (univ.filter fun a => ep a = false).card

def Decay : Prop :=
  ∀ (N : ℕ) (s : ℕ → ℝ) (ep : Fin N → Bool) (h : ℝ) (Y : Matrix (Fin N) (Fin N) ℂ),
    (∀ i, 0 ≤ s i) → Y.IsHermitian → (∀ a b, ep a = ep b → Y a b = 0) →
    (∀ a b : Fin N, b < a → ep a ≠ ep b → h ≤ ∑ i ∈ Ico (b.val + 1) (a.val + 1), s i) →
    ∏ i ∈ Ico 1 N, (lead (NormedSpace.exp Y) i).re ^ (-(s i))
      ≤ Real.exp (-(h * min (hs Y ^ 2) (hs Y / Real.sqrt (2 * (q0 ep : ℝ)))) / 8)

end Formalism.NuclearRankWeightBounds.D
