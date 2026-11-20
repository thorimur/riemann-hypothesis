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

noncomputable section

namespace GlobalTheory.DblUnip

open Matrix

variable {R : Type} [CommRing R] {d : ℕ}

def unipMat (c : R →+* R) (J : Matrix (Fin d) (Fin d) R) (x₀ y₀ : Fin d → R) (β : R) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R :=
  fromBlocks 1 (β • vecMulVec x₀ (J *ᵥ fun i => c (y₀ i))) (-(c β) • vecMulVec y₀ (J *ᵥ fun i => c (x₀ i))) 1

def diagMat (c : R →+* R) (J : Matrix (Fin d) (Fin d) R) (x₀ y₀ : Fin d → R) (β : R) : Matrix (Fin d) (Fin d) R :=
  1 - c β • vecMulVec y₀ (J *ᵥ fun i => c (x₀ i))

end GlobalTheory.DblUnip

end
