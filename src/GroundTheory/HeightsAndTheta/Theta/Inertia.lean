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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Matrix Module

variable {ι : Type*} [Fintype ι]

noncomputable def hermQuad (A : Matrix ι ι ℂ) (x : ι → ℂ) : ℝ := (star x ⬝ᵥ (A *ᵥ x)).re

def IsPosSubspace (A : Matrix ι ι ℂ) (W : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → 0 < hermQuad A x

noncomputable def posIndex (A : Matrix ι ι ℂ) : ℕ :=
  sSup {r | ∃ W : Submodule ℂ (ι → ℂ), IsPosSubspace A W ∧ finrank ℂ W = r}

noncomputable def negIndex (A : Matrix ι ι ℂ) : ℕ := posIndex (-A)

noncomputable def matrixSignature (A : Matrix ι ι ℂ) : ℕ × ℕ := (posIndex A, negIndex A)

section Index

variable (A : Matrix ι ι ℂ)

end Index

section Congruence

variable [DecidableEq ι]

end Congruence

section Diagonal

variable [DecidableEq ι]

end Diagonal

section Hermitian

variable [DecidableEq ι] {A : Matrix ι ι ℂ}

end Hermitian

end GroundTheory.Heights₂.Theta
