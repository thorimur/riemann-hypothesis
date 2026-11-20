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
import Mathlib.LinearAlgebra.Matrix.PosDef
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

open Complex Matrix

namespace ReciprocityTheory.PTheta

def eC (x : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

variable {ι : Type*} [Fintype ι]

def SiegelH (ι : Type*) [Fintype ι] : Set (Matrix ι ι ℂ) :=
  {τ | τ.IsSymm ∧ (τ.map Complex.im).PosDef}

def ThetaDomain (ι : Type*) [Fintype ι] : Set (Matrix ι ι ℂ) :=
  {τ | (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef}

def ofRealVec (a : ι → ℝ) : ι → ℂ := fun i => (a i : ℂ)

def ofIntVec (n : ι → ℤ) : ι → ℂ := fun i => (n i : ℂ)

theorem ofIntVec_add (n m : ι → ℤ) : ofIntVec (n + m) = ofIntVec n + ofIntVec m := by
  ext i; simp [ofIntVec]

theorem ofIntVec_neg (n : ι → ℤ) : ofIntVec (-n) = -ofIntVec n := by
  ext i; simp [ofIntVec]

theorem ofIntVec_zero : ofIntVec (0 : ι → ℤ) = 0 := by
  ext i; simp [ofIntVec]

def shiftVec (a : ι → ℝ) (l : ι → ℤ) : ι → ℂ := fun i => (l i : ℂ) + (a i : ℂ)

def thetaTerm (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ) (l : ι → ℤ) : ℂ :=
  eC (shiftVec a l ⬝ᵥ (τ *ᵥ shiftVec a l) / 2 + shiftVec a l ⬝ᵥ (z + ofRealVec b))

def theta (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ) : ℂ :=
  ∑' l : ι → ℤ, thetaTerm a b z τ l

def autFactor (a b : ι → ℝ) (τ : Matrix ι ι ℂ) (n n' : ι → ℤ) (z : ι → ℂ) : ℂ :=
  eC (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n) *
    eC (-(ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n)) / 2 - ofIntVec n ⬝ᵥ z)

def periodLattice (τ : Matrix ι ι ℂ) : AddSubgroup (ι → ℂ) where
  carrier := {w | ∃ n n' : ι → ℤ, w = τ *ᵥ ofIntVec n + ofIntVec n'}
  add_mem' := by
    rintro _ _ ⟨n, n', rfl⟩ ⟨m, m', rfl⟩
    refine ⟨n + m, n' + m', ?_⟩
    rw [ofIntVec_add, ofIntVec_add, Matrix.mulVec_add]; abel
  zero_mem' := ⟨0, 0, by rw [ofIntVec_zero, Matrix.mulVec_zero, add_zero]⟩
  neg_mem' := by
    rintro _ ⟨n, n', rfl⟩
    refine ⟨-n, -n', ?_⟩
    rw [ofIntVec_neg, ofIntVec_neg, Matrix.mulVec_neg]; abel

end ReciprocityTheory.PTheta
