import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal :
    ∀ {σ : Type} (X : σ → Scheme.{0}) {V : Scheme.{0}} (a : V ⟶ ∐ X) (x : V), ∃ (U : V.Opens) (p : σ) (a₁ : (U : Scheme.{0}) ⟶ X p), x ∈ U ∧ U.ι ≫ a = a₁ ≫ Sigma.ι X p := by
  intro σ X V a x
  obtain ⟨⟨p, z⟩, hz⟩ := (sigmaMk X).surjective (a x)
  rw [sigmaMk_mk] at hz
  have hr : Set.range ((a ⁻¹ᵁ (Sigma.ι X p).opensRange).ι ≫ a) ⊆ Set.range (Sigma.ι X p) := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  refine ⟨a ⁻¹ᵁ (Sigma.ι X p).opensRange, p,
    IsOpenImmersion.lift (Sigma.ι X p) ((a ⁻¹ᵁ (Sigma.ι X p).opensRange).ι ≫ a) hr, ?_, ?_⟩
  · show a x ∈ (Sigma.ι X p).opensRange
    exact ⟨z, hz⟩
  · exact (IsOpenImmersion.lift_fac _ _ _).symm
