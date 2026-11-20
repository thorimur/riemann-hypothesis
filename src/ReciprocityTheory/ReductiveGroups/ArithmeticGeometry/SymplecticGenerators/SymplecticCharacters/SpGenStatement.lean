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
import Mathlib.LinearAlgebra.SymplecticGroup
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

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

def spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks 1 S 0 1

def spDiag {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks (U : Matrix (Fin g) (Fin g) ℤ) 0 0 ((↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ)ᵀ)

def spGens (g : ℕ) : Set (Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :=
  {M | ∃ S : Matrix (Fin g) (Fin g) ℤ, S.IsSymm ∧ M = spTransl S} ∪
    {M | ∃ U : (Matrix (Fin g) (Fin g) ℤ)ˣ, M = spDiag U} ∪ {J (Fin g) ℤ}

def SpGenStatement : Prop :=
  ∀ g : ℕ, ∀ M ∈ symplecticGroup (Fin g) ℤ, M ∈ Submonoid.closure (spGens g)

end ReciprocityTheory.ChartRestriction.G.Key.Chi
