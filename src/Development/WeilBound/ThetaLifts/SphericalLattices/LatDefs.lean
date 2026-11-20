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
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k]

def IntM {m p : Type} (Z : Matrix m p k) : Prop := ∀ i j, Z i j ∈ 𝒪[k]

def Below {n d : ℕ} (t : k) (Y Y₀ : Matrix (Fin n) (Fin d) k) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) 𝒪[k], ∃ Z : Matrix (Fin n) (Fin d) k, IntM Z ∧
    Y = A.map (algebraMap 𝒪[k] k) * Y₀ + t • Z

def latt {n d : ℕ} (t : k) (Y₀ : Matrix (Fin n) (Fin d) k) : Submodule 𝒪[k] (Fin d → k) :=
  Submodule.span 𝒪[k] (Set.range Y₀ ∪ Set.range fun j : Fin d => t • (Pi.single j 1 : Fin d → k))

end PositivityTheory.Sph

end
