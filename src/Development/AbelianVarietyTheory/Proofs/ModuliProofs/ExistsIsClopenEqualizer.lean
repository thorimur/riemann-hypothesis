import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
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

open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.ClopenEqualizer

theorem exists_isClopen_equalizer {P C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (a b : P ⟶ C)
    (h : a ≫ c = b ≫ c) :
    ∃ (U : Set P), IsClopen U ∧ ∀ (T : Scheme.{0}) (y : T ⟶ P), y ≫ a = y ≫ b ↔ Set.range y ⊆ U := by
  let d := pullback.diagonal c
  let l : P ⟶ pullback c c := pullback.lift a b h
  haveI : IsOpenImmersion d := inferInstance
  haveI : IsClosedImmersion d := inferInstance
  let j : pullback l d ⟶ P := pullback.fst l d
  have hj : j ≫ a = j ≫ b := by
    have h0 : j ≫ l = pullback.snd l d ≫ d := pullback.condition
    have h1 := congrArg (· ≫ pullback.fst c c) h0
    have h2 := congrArg (· ≫ pullback.snd c c) h0
    simp [l, d, pullback.lift_fst, pullback.lift_snd] at h1 h2
    rw [h1, h2]
  refine ⟨Set.range j, ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩, ?_⟩
  intro T y
  constructor
  · intro hy
    have e : y ≫ l = (y ≫ a) ≫ d := by
      apply pullback.hom_ext
      · simp [l, d, pullback.lift_fst]
      · simp [l, d, hy, pullback.lift_snd]
    have e2 : pullback.lift y (y ≫ a) e ≫ j = y := pullback.lift_fst _ _ _
    rintro _ ⟨t, rfl⟩
    refine ⟨pullback.lift y (y ≫ a) e t, ?_⟩
    rw [← Scheme.Hom.comp_apply, e2]
  · intro hy
    rw [← IsOpenImmersion.lift_fac j y hy, Category.assoc, Category.assoc, hj]

end GlobalTheory.ClopenEqualizer
