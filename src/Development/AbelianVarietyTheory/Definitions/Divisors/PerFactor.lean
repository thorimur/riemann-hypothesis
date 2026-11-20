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
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
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
noncomputable section
namespace GlobalTheory.PolDeg.Taut
variable (W : Type) [CommRing W] [IsDomain W]

def coordT (m N : ℕ) (k : Fin N) : MvPowerSeries (Fin N) W :=
  if (k : ℕ) < m then MvPowerSeries.X k else 1 + MvPowerSeries.X k

def params {m N : ℕ} (h : m ≤ N) : Fin m → MvPowerSeries (Fin N) W := fun i => MvPowerSeries.X (Fin.castLE h i)

def perFactor (m N n r : ℕ) (ε : Fin N → LinearMap.BilinForm ℤ (Fin r → ℤ)) (a b : Fin r → ℤ) : FractionRing (MvPowerSeries (Fin N) W) :=
  ∏ k, (algebraMap (MvPowerSeries (Fin N) W) (FractionRing (MvPowerSeries (Fin N) W)) (coordT W m N k)) ^ ((n : ℤ) * ε k a b)
example : perFactor W 0 0 3 0 (fun k => k.elim0) 0 0 = 1 := by simp [perFactor]
end GlobalTheory.PolDeg.Taut
