import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

def IsHilbRep {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) : Prop :=
  ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧
    IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧
    ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v →
      IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) →
      ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U,
        IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u

end GlobalTheory.HilbertSch
