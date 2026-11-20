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
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory.NormalDescent

open Polynomial TensorProduct

variable {A B : Type} [CommRing A] [CommRing B]

def charK (φ : A →+* B) (hφ : φ.Finite) (K : Type) [Field K] [Algebra A K] (b : B) : K[X] :=
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly

def normCoeff [IsDomain A] (φ : A →+* B) (hφ : φ.Finite) (b : B) (k : ℕ) : A :=
  letI := Classical.propDecidable
  if h : ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k then
    h.choose else 0

theorem algebraMap_normCoeff [IsDomain A] (φ : A →+* B) (hφ : φ.Finite) (b : B) (k : ℕ)
    (h : ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k) :
    algebraMap A (FractionRing A) (normCoeff φ hφ b k) = (charK φ hφ (FractionRing A) b).reverse.coeff k := by
  classical
  unfold normCoeff
  rw [dif_pos h]
  exact h.choose_spec

theorem charK_monic (φ : A →+* B) (hφ : φ.Finite) (K : Type) [Field K] [Algebra A K] (b : B) :
    (charK φ hφ K b).Monic := by
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  exact LinearMap.charpoly_monic _

end GlobalTheory.NormalDescent
