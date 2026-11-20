import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem localization_away_descent_range :
 ∀ (k : Type) [Field k] (P : Polynomial k) (T : Finset (Localization.Away P)), ∃ F : Finset k, ∀ (R : Subring k), (F : Set k) ⊆ R → ∀ (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → ∀ t ∈ T, t ∈ (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h).range := by
  classical
  intro k _ P T
  have hs : ∀ t : Localization.Away P, ∃ (f : Polynomial k) (n : ℕ),
      IsLocalization.mk' (Localization.Away P) f
        (⟨P ^ n, n, rfl⟩ : Submonoid.powers P) = t := by
    intro t
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers P) t
    obtain ⟨n, hn⟩ := s.2
    exact ⟨f, n, by congr 1; exact Subtype.ext hn⟩
  choose f n hfn using hs
  refine ⟨T.biUnion (fun t => (f t).coeffs), ?_⟩
  intro R hF P₁ h hP t ht
  have hlift : f t ∈ Polynomial.lifts R.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro m
    by_cases hm : (f t).coeff m = 0
    · exact ⟨0, by simp [hm]⟩
    · have : (f t).coeff m ∈ (T.biUnion (fun t => (f t).coeffs) : Set k) := by
        simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
        exact ⟨t, ht, Polynomial.coeff_mem_coeffs hm⟩
      exact ⟨⟨_, hF this⟩, rfl⟩
  obtain ⟨f₁, hf₁⟩ := (Polynomial.mem_lifts _).mp hlift
  refine ⟨IsLocalization.mk' (Localization.Away P₁) f₁
    (⟨P₁ ^ n t, n t, rfl⟩ : Submonoid.powers P₁), ?_⟩
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, hf₁,
    Polynomial.map_pow, hP]
  have key := IsLocalization.mk'_spec' (Localization.Away P) (f t)
    (⟨P ^ n t, n t, rfl⟩ : Submonoid.powers P)
  rw [hfn t] at key
  exact key.symm

end GlobalTheory
