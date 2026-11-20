import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.PullbackRestrict

theorem isPullback_restrict_opens :
    ∀ {P Q Y S : Scheme.{0}} {c : P ⟶ Q} {v : P ⟶ Y} {g : Q ⟶ S} {p : Y ⟶ S},
      IsPullback c v g p → ∀ (W : S.Opens) (D : Y.Opens), D ≤ p ⁻¹ᵁ W →
        ∃ (h : D.toScheme ⟶ W.toScheme) (u : (v ⁻¹ᵁ D).toScheme ⟶ (g ⁻¹ᵁ W).toScheme),
          IsPullback u (v ∣_ D) (g ∣_ W) h := by
  intro P Q Y S c v g p H W D hD
  have hbot : (Y.homOfLE hD ≫ p ∣_ W) ≫ W.ι = D.ι ≫ p := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have s : IsPullback ((v ⁻¹ᵁ D).ι ≫ c) (v ∣_ D) g ((Y.homOfLE hD ≫ p ∣_ W) ≫ W.ι) := by
    rw [hbot]
    exact (isPullback_morphismRestrict v D).flip.paste_horiz H
  exact ⟨_, _, IsPullback.of_right' s (isPullback_morphismRestrict g W).flip⟩

end GlobalTheory.CompanionTheory.PullbackRestrict
