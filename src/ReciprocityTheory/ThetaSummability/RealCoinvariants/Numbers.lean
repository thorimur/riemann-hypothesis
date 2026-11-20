import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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

noncomputable section

namespace ReciprocityTheory.ThetaSummability.Real

structure RealData where
  a : ℕ
  a' : ℕ
  p : ℕ
  q : ℕ
  κ : ℕ

structure RealData.Hyp (D : RealData) : Prop where
  a_gt : D.a' < D.a
  a'_pos : 1 ≤ D.a'
  even_im_hermitian_sub : (D.a - D.a') % 2 = 0
  h1a : 2 * D.p + 1 ≤ D.a
  h1b : 2 * D.q + 1 ≤ D.a'
  h2 : D.a + D.a' < D.κ
  h3 : D.κ % 2 = 0
  h5 : 2 * (D.p + D.q) < D.a'
  h4 : 2 * D.p + D.a' < D.a

namespace RealData

variable (D : RealData)

def d : ℕ := D.a + D.a'
def y : ℕ := D.p + D.q
def R : ℕ := D.d - D.y
def S : ℕ := D.y
def P : ℕ := D.a - D.p
def Q : ℕ := D.p
def P' : ℕ := D.q
def Q' : ℕ := D.a' - D.q
def e : ℝ := ((D.a : ℝ) - D.a') / 2
def c₁ : ℝ := ((D.R : ℝ) - D.S) / 2
def c₂ : ℝ := ((D.P : ℝ) - D.Q) / 2
def c₂' : ℝ := ((D.P' : ℝ) - D.Q') / 2
def x₁ : ℝ := (D.κ : ℝ) / 2 - D.c₁ + D.c₂
def x₂ : ℝ := D.c₂
def y₁ : ℝ := (D.κ : ℝ) / 2 + D.c₁ - D.c₂
def y₂ : ℝ := -D.c₂

def ω : ℝ := D.x₁ - D.y₂

def ω' : ℝ := D.y₁ - D.x₂

end RealData

def exampleData : RealData := ⟨9, 5, 1, 1, 16⟩

theorem exampleData_hyp : exampleData.Hyp := by
  constructor <;> norm_num [exampleData]

end ReciprocityTheory.ThetaSummability.Real
