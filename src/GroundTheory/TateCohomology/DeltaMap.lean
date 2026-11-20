import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
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
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

noncomputable def cochainsMapShortComplex (f : G →* H) {X : ShortComplex (Rep k H)}
    {Y : ShortComplex (Rep k G)} (F : X.map (resFunctor f) ⟶ Y) :
    X.map (cochainsFunctor k H) ⟶ Y.map (cochainsFunctor k G) where
  τ₁ := cochainsMap f F.τ₁
  τ₂ := cochainsMap f F.τ₂
  τ₃ := cochainsMap f F.τ₃
  comm₁₂ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₁₂
  comm₂₃ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₂₃

theorem δ_comp_map (f : G →* H) {X : ShortComplex (Rep k H)} {Y : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (hY : Y.ShortExact) (F : X.map (resFunctor f) ⟶ Y)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f F.τ₁ j = map f F.τ₃ i ≫ δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsMapShortComplex f F)
    (map_cochainsFunctor_shortExact hX) (map_cochainsFunctor_shortExact hY) i j hij

theorem δ_comp_map_res (f : G →* H) {X : ShortComplex (Rep k H)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f (𝟙 (res f X.X₁)) j =
      map f (𝟙 (res f X.X₃)) i ≫ δ ((shortExact_res f).2 hX) i j hij :=
  δ_comp_map f hX ((shortExact_res f).2 hX) (𝟙 _) i j hij

end GroundTheory.GroupCoh
