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

namespace Formalism.L2.SG.Pf.Lem3Mass

open Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds Filter Topology

section Alg

variable {R : Type} [CommRing R] [StarRing R] {m : ℕ}

def Mult (c : R) (N : ℕ) : Set (Matrix (Fin m) (Fin m) R) := {X | ∃ W, X = c ^ N • W}

variable {c : R}

end Alg

section Top

variable {R : Type} [CommRing R] [StarRing R] [TopologicalSpace R] [IsTopologicalRing R] [ContinuousStar R]
  [CompactSpace R] [T2Space R] {m : ℕ}

instance compactSpace_matR : CompactSpace (Matrix (Fin m) (Fin m) R) :=
  inferInstanceAs (CompactSpace (Fin m → Fin m → R))

instance t2SpaceMatrix : T2Space (Matrix (Fin m) (Fin m) R) := inferInstanceAs (T2Space (Fin m → Fin m → R))

end Top

end Formalism.L2.SG.Pf.Lem3Mass
