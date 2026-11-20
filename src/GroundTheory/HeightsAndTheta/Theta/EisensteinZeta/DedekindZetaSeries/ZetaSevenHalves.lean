import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.DedekindZeta
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

open NumberField

noncomputable section

def zetaSevenHalves : ℝ :=
  (riemannZeta (7 / 2 : ℂ)).re

def ZetaSevenHalvesBounds.Value.Statement : Prop :=
  riemannZeta (7 / 2 : ℂ) = (zetaSevenHalves : ℂ) ∧
    (1.1267 : ℝ) ≤ zetaSevenHalves ∧ zetaSevenHalves < (1.1268 : ℝ)

def ZetaSevenHalvesBounds.LogBound.Statement : Prop :=
  Real.log zetaSevenHalves ≤ (0.13 : ℝ)

def ZetaSevenHalvesBounds.TwiceLogBound.Statement : Prop :=
  2 * Real.log zetaSevenHalves ≤ (0.26 : ℝ)

def ZetaSevenHalvesBounds.DedekindBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Real.log (dedekindZeta K (7 / 2 : ℂ)).re ≤
      (Module.finrank ℚ K : ℝ) * Real.log zetaSevenHalves

end

end GroundTheory.Heights₂.Theta
