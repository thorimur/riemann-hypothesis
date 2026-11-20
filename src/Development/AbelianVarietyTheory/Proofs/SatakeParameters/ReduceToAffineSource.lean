import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
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
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtDescentAff

variable {X U Y : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U)
  (θ : ∀ (T : Scheme.{0}) (a b : T ⟶ U), a ≫ u = b ≫ u →
    {y : T ⟶ Y // y ≫ p = a} → {y : T ⟶ Y // y ≫ p = b})

def Rel {T : Scheme.{0}} (y₁ y₂ : T ⟶ Y) : Prop :=
  ∃ h : (y₁ ≫ p) ≫ u = (y₂ ≫ p) ≫ u, (θ T (y₁ ≫ p) (y₂ ≫ p) h ⟨y₁, rfl⟩).1 = y₂

variable {u p θ}

end GlobalTheory.EtDescentAff

namespace GlobalTheory.EtDescentAff

variable {X U Y : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U)
  (θ : ∀ (T : Scheme.{0}) (a b : T ⟶ U), a ≫ u = b ≫ u →
    {y : T ⟶ Y // y ≫ p = a} → {y : T ⟶ Y // y ≫ p = b})

noncomputable def thetaPull {U' : Scheme.{0}} (ι : U' ⟶ U) (T : Scheme.{0}) (a b : T ⟶ U')
    (h : a ≫ (ι ≫ u) = b ≫ (ι ≫ u))
    (y : {y : T ⟶ pullback p ι // y ≫ pullback.snd p ι = a}) :
    {y : T ⟶ pullback p ι // y ≫ pullback.snd p ι = b} :=
  ⟨pullback.lift (θ T (a ≫ ι) (b ≫ ι) (by simpa only [Category.assoc] using h)
      ⟨y.1 ≫ pullback.fst p ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩).1 b
    (θ T (a ≫ ι) (b ≫ ι) (by simpa only [Category.assoc] using h)
      ⟨y.1 ≫ pullback.fst p ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩).2,
    pullback.lift_snd _ _ _⟩

variable {u p θ}

end GlobalTheory.EtDescentAff

namespace GlobalTheory.EtDescentAff

end GlobalTheory.EtDescentAff
