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

open Metric Set
open scoped Nat ContDiff

namespace GlobalTheory.SCV

section Polarisation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {𝕜 E V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

end Polarisation

section OpNorm

variable {ι 𝕜 E V : Type*} [Fintype ι] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

end OpNorm

section Homogeneous

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def homogeneousPart (c : ℕ) (F : E → V) (a : E) (v : E) : V :=
  (c ! : ℂ)⁻¹ • iteratedFDeriv ℂ c F a (fun _ => v)

@[simp] theorem homogeneousPart_zero (F : E → V) (a v : E) : homogeneousPart 0 F a v = F a := by
  simp [homogeneousPart]

variable [FiniteDimensional ℂ E] [CompleteSpace V]

end Homogeneous

end GlobalTheory.SCV
