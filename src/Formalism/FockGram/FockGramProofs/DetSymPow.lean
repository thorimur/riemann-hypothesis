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

open Finset Matrix MvPolynomial

noncomputable section

namespace Formalism.E

section SlopeTestRemainingChoices

variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

def spLin (A : Matrix σ σ R) (i : σ) : MvPolynomial σ R := ∑ j, C (A i j) * X j

def spRow (A : Matrix σ σ R) (s : Multiset σ) : MvPolynomial σ R := (s.map (spLin A)).prod

def spHom (A : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := aeval (spLin A)

end SlopeTestRemainingChoices

section Field

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K] [CharZero K]

end Field

def genMat (σ : Type*) : Matrix σ σ (MvPolynomial (σ × σ) ℤ) := Matrix.of fun i j => X (i, j)

end Formalism.E
