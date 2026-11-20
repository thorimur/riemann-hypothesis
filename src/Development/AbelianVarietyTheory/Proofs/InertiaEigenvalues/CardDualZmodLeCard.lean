import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem card_dual_zmod_le_card :
    ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A],
      Nat.card (Module.Dual (ZMod n) A) ≤ Nat.card A := by
  intro n _ A _ _ _
  classical
  haveI : Fintype A := Fintype.ofFinite A
  let Φ : Module.Dual (ZMod n) A → AddChar A ℂ := fun f =>
    (ZMod.stdAddChar (N := n)).compAddMonoidHom f.toAddMonoidHom
  have hinj : Function.Injective Φ := by
    intro f g h
    ext a
    have h1 := congrArg (fun χ : AddChar A ℂ => χ a) h
    simp only [Φ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at h1
    exact ZMod.injective_stdAddChar h1
  calc Nat.card (Module.Dual (ZMod n) A) ≤ Nat.card (AddChar A ℂ) :=
        Nat.card_le_card_of_injective Φ hinj
    _ = Nat.card A := by
        rw [Nat.card_eq_fintype_card, AddChar.card_eq, Nat.card_eq_fintype_card]

end GlobalTheory
