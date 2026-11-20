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
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_quotient_form_eq_eval :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
      [Module.Projective O M] (I : Ideal O) (u : Module.Dual O M →ₗ[O] O ⧸ I),
      ∃ b : M, ∀ φ, u φ = Ideal.Quotient.mk I (φ b) := by
  intro O M _ _ _ _ _ I u
  obtain ⟨v, hv⟩ := Module.projective_lifting_property (Submodule.mkQ I) u
    (Submodule.mkQ_surjective I)
  refine ⟨(Module.evalEquiv O M).symm v, fun φ => ?_⟩
  have h1 : φ ((Module.evalEquiv O M).symm v) = v φ := by
    have := congrArg (fun w : Module.Dual O (Module.Dual O M) => w φ)
      ((Module.evalEquiv O M).apply_symm_apply v)
    simpa using this
  rw [h1, ← hv]
  rfl

end GlobalTheory
