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
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
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

open NumberField NumberField.InfinitePlace

namespace Formalism.IndefR.Leaf.HaarTransferContinuity

variable (F : Type) [Field F] [NumberField F]

abbrev W := ({v : InfinitePlace F // v.IsReal} → ℝ) × ({v : InfinitePlace F // ¬ v.IsReal} → ℂ)

noncomputable def E (x : InfiniteAdeleRing F) : W F :=
  (fun v => Completion.extensionEmbeddingOfIsReal v.2 (x v.1),
   fun v => Completion.extensionEmbedding v.1 (x v.1))

open scoped Classical in
noncomputable def G (w : W F) : InfiniteAdeleRing F := fun v =>
  if h : v.IsReal then (Completion.isometryEquivRealOfIsReal h).symm (w.1 ⟨v, h⟩)
  else (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp h)).symm (w.2 ⟨v, h⟩)

end Formalism.IndefR.Leaf.HaarTransferContinuity
