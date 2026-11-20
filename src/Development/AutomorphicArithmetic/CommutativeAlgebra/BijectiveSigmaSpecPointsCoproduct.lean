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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open AlgebraicGeometry CategoryTheory Limits

theorem UpperTheory.bijective_sigma_spec_points_coproduct :
    ∀ {I : Type} (Z : I → Scheme.{0}) (K : Type) [Field K], Function.Bijective (fun p : (Σ c, (Spec (CommRingCat.of K) ⟶ Z c)) => p.2 ≫ Sigma.ι Z p.1) := by
  intro I Z K _
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  constructor
  · rintro ⟨c, f⟩ ⟨c', f'⟩ h
    simp only at h
    have hz : (Sigma.ι Z c) (f z) = (Sigma.ι Z c') (f' z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
    have hs := (sigmaι_eq_iff Z c c' (f z) (f' z)).mp hz
    obtain ⟨rfl, -⟩ := Sigma.mk.inj hs
    have hff : f = f' := (cancel_mono (Sigma.ι Z c)).mp h
    rw [hff]
  · intro f
    obtain ⟨⟨c, y⟩, hy⟩ := (sigmaMk Z).surjective (f z)
    rw [sigmaMk_mk] at hy
    have H : Set.range f ⊆ Set.range (Sigma.ι Z c) := by
      rintro _ ⟨w, rfl⟩
      exact ⟨y, by rw [hy, Subsingleton.elim w z]⟩
    exact ⟨⟨c, IsOpenImmersion.lift (Sigma.ι Z c) f H⟩, IsOpenImmersion.lift_fac _ _ _⟩
