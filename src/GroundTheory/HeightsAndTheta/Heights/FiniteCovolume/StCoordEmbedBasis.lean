import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

noncomputable section

variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]

def coordEmbed : (ι → E) →+ (InfinitePlace E → ι → ℂ) where
  toFun y := fun w i => w.embedding (y i)
  map_zero' := by funext w i; simp
  map_add' y z := by funext w i; simp

omit [Fintype ι] in
theorem coordEmbed_apply (y : ι → E) (w : InfinitePlace E) (i : ι) :
    coordEmbed E ι y w i = w.embedding (y i) := rfl

def CoordEmbedBasis.Statement [IsTotallyComplex E] : Prop :=
  LinearIndependent ℝ (fun k => coordEmbed E ι (Pi.basis (fun _ : ι => integralBasis E) k)) ∧
    finrank ℝ (InfinitePlace E → ι → ℂ) = finrank ℚ (ι → E)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
