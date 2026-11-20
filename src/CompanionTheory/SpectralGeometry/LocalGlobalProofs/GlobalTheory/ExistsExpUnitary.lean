import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
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

namespace GlobalTheory.CompanionTheory.UnitaryExp

open Matrix

set_option backward.isDefEq.respectTransparency false in

theorem map_exp_matrix {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (f : Matrix m m ℂ ≃ₐ[ℂ] Matrix n n ℂ) (hf : Continuous f) (S : Matrix m m ℂ) :
    f (NormedSpace.exp S) = NormedSpace.exp (f S) := by
  let _ : NormedRing (Matrix m m ℂ) := Matrix.instL2OpNormedRing
  let _ : NormedRing (Matrix n n ℂ) := Matrix.instL2OpNormedRing
  let _ : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.instL2OpNormedAlgebra
  let _ : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.instL2OpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix m m ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp f hf S

end GlobalTheory.CompanionTheory.UnitaryExp
