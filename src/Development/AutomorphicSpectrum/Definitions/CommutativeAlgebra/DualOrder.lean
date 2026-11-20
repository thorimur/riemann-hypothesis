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

namespace GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] {T H : Type} [CommGroup T] [CommGroup H]

def pullFun (R : Type) [CommRing R] (ι : H →* T) : (T → R) →ₐ[R] (H → R) :=
  Pi.algHom R _ fun h => Pi.evalAlgHom R (fun _ : T => R) (ι h)

def resOrder (ι : H →* T) (A : Subalgebra R (T → R)) : Subalgebra R (H → R) := A.map (pullFun R ι)

def quotOrder (π : T →* H) (A : Subalgebra R (T → R)) : Subalgebra R (H → R) := A.comap (pullFun R π)

def muOrder (R : Type) [CommRing R] (T : Type) [CommGroup T] : Subalgebra R (T → R) :=
  Algebra.adjoin R {f | ∃ χ : T →* Rˣ, f = fun t => ((χ t : Rˣ) : R)}

def dualOrder (A : Subalgebra R (T → R)) : Subalgebra R ((T →* Rˣ) → R) :=
  Algebra.adjoin R {g | ∃ l : A →ₗ[R] R, ∀ (χ : T →* Rˣ) (h : (fun t => ((χ t : Rˣ) : R)) ∈ A), g χ = l ⟨_, h⟩}

end GlobalTheory.CompanionTheory.Ar.BT
