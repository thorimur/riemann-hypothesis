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

namespace Formalism.MainNotions.Gaps.RN

def LenBaseChangeDVR : Prop :=
  ∀ (A O : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (f : A →+* O), IsLocalHom f → Function.Injective f →
    ∀ (ϖ : A), Irreducible ϖ → ∀ (ι : Type) [Fintype ι] (N : Submodule A (ι → A)),
      Module.length O ((ι → O) ⧸ Submodule.span O ((fun x : ι → A => f ∘ x) '' (N : Set (ι → A)))) =
        ((IsDiscreteValuationRing.addVal O (f ϖ)).toNat : ℕ∞) * Module.length A ((ι → A) ⧸ N)

end Formalism.MainNotions.Gaps.RN
