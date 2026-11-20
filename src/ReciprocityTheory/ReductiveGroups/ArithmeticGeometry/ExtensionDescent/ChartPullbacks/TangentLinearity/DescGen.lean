import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.Fpqc
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

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

theorem descend_gen {X Y : Scheme.{0}} (Q : X ⟶ Y) [Flat Q] [Surjective Q] [IsAffineHom Q]
    (ρ : Γ(X, ⊤))
    (hρ : ∀ {Z : Scheme.{0}} (y1 y2 : Z ⟶ X), y1 ≫ Q = y2 ≫ Q → y1.appTop.hom ρ = y2.appTop.hom ρ) :
    ∃ v : Γ(Y, ⊤), Q.appTop.hom v = ρ := by

  have hE : EffectiveEpi Q := by
    exact inferInstance

  obtain ⟨e, he⟩ : ∃ e, ∀ i : Fin 1, AffineSpace.toSpecMvPolyIntEquiv (Fin 1) e i = ρ :=
    ⟨(AffineSpace.toSpecMvPolyIntEquiv (Fin 1)).symm fun _ => ρ, fun i => by simp⟩
  have hcomp : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (i : Fin 1),
      AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (g ≫ e) i = g.appTop.hom ρ := by
    intro Z g i
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp, he]
  have hdesc : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ X), g₁ ≫ Q = g₂ ≫ Q → g₁ ≫ e = g₂ ≫ e := by
    intro Z g₁ g₂ h
    apply (AffineSpace.toSpecMvPolyIntEquiv (Fin 1)).injective
    funext i
    rw [hcomp, hcomp]
    exact hρ g₁ g₂ h
  refine ⟨AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (EffectiveEpi.desc Q e hdesc) 0, ?_⟩
  have hf : AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (Q ≫ EffectiveEpi.desc Q e hdesc) 0 = ρ := by
    rw [EffectiveEpi.fac, he]
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp] at hf
  exact hf

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
