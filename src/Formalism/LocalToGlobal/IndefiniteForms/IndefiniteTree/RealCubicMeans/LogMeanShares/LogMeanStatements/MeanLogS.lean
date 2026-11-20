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

open NumberField

namespace Formalism.NormVectorIdentities.Items

section abelian₂

variable {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

def vecS (b : Module.Basis ι K V) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  fun i => v.embedding (b.repr x i)

def fcoordS (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  Matrix.mulVec (X v)⁻¹ (vecS b v x)

def cnormS (u : ι → ℂ) : ℝ := Real.sqrt (∑ i, ‖u i‖ ^ 2)

def normS (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) : ℝ :=
  cnormS (fcoordS b X v x)

variable (K) in

def nPlS : ℕ := Fintype.card (InfinitePlace K)

end abelian₂

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}

def meanLogS (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) : ℝ :=
  (1 / (nPlS K : ℝ)) * ∑ v, Real.log (normS (Pi.basisFun K (Fin n)) X v x ^ 2)

def LamS (M : Submodule (𝓞 K) (Fin n → K)) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (La : ℝ) : Prop :=
  ∀ x ∈ M, x ≠ 0 → -(2 * La) ≤ meanLogS X x

end Formalism.NormVectorIdentities.Items
