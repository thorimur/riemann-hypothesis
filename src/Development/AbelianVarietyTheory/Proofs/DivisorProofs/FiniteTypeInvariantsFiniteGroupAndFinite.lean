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

namespace GlobalTheory

theorem finiteType_invariants_and_finite (R : Type) [CommRing R] [IsNoetherianRing R]
    (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C']
    (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C')
    (hC : ∀ x, x ∈ C ↔ ∀ σ, act σ x = x) :
    Algebra.FiniteType R C ∧ Module.Finite C C' := by
  letI : MulSemiringAction G C' := MulSemiringAction.compHom C' act
  haveI : Algebra.IsInvariant C C' G := ⟨fun b hb => ⟨⟨b, (hC b).2 fun σ => hb σ⟩, rfl⟩⟩
  haveI : Algebra.IsIntegral C C' := Algebra.IsInvariant.isIntegral C C' G
  haveI : Algebra.FiniteType C C' := Algebra.FiniteType.of_restrictScalars_finiteType R C C'
  haveI hfin : Module.Finite C C' := Algebra.IsIntegral.finite
  refine ⟨⟨fg_of_fg_of_fg (A := R) (B := C) (C := C') Algebra.FiniteType.out
    hfin.fg_top Subtype.val_injective⟩, hfin⟩

end GlobalTheory
