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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.Mod

theorem spPaste : ∀ {Y S A B C : Scheme.{0}} (p : Y ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : C ⟶ A) (d : C ⟶ B), c ≫ a = d ≫ b → ∀ φ : pullback (pullback.snd p b) d ⟶ pullback p a, φ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ → φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ c → IsPullback φ (pullback.snd _ _) (pullback.snd _ _) c := by
  intro Y S A B C p a b c d h φ h1 h2
  have big : IsPullback (pullback.fst (pullback.snd p b) d ≫ pullback.fst p b)
      (pullback.snd (pullback.snd p b) d) p (d ≫ b) :=
    (IsPullback.of_hasPullback (pullback.snd p b) d).paste_horiz
      (IsPullback.of_hasPullback p b)
  have big' : IsPullback (φ ≫ pullback.fst p a)
      (pullback.snd (pullback.snd p b) d) p (c ≫ a) := by
    rw [h1, h]; exact big
  exact IsPullback.of_right big' h2 (IsPullback.of_hasPullback p a)

end UpperTheory.Gal.Mod
