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
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
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

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FlatTheorem

open NumberField

noncomputable def rootDisc (F : Type*) [Field F] [NumberField F] : ℝ :=
  |(discr F : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ F : ℝ))

theorem rootDisc_rat : rootDisc ℚ = 1 := by
  simp [rootDisc]

def RootDiscriminantMonotone.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E],
    rootDisc K ≤ rootDisc E

theorem RootDiscriminantMonotone.inhabitant : Nonempty (Algebra ℚ (CyclotomicField 4 ℚ)) :=
  ⟨inferInstance⟩

structure FlatDegreeFormula (K E : Type*) [Field K] [NumberField K] [Field E]
    [NumberField E] where

  p : ℕ

  q' : ℕ

  logOm : ℝ

  d : ℝ

  formula : d = ((p : ℝ) - q') / 2 * logOm +
    q' * (2 * Real.log (rootDisc K) - Real.log (rootDisc E))

noncomputable def FlatDegreeFormula.inhabitant : FlatDegreeFormula ℚ (CyclotomicField 4 ℚ) where
  p := 2
  q' := 1
  logOm := 1
  d := (((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) / 2 * 1 +
    ((1 : ℕ) : ℝ) * (2 * Real.log (rootDisc ℚ) - Real.log (rootDisc (CyclotomicField 4 ℚ)))
  formula := rfl

def FlatDegreeBound.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (D : FlatDegreeFormula K E),
    |-D.d + ((D.p : ℝ) - D.q') / 2 * D.logOm| ≤ D.q' * Real.log (rootDisc E)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FlatTheorem
