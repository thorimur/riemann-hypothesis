import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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

open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isProper_of_finite_cover (X S : Scheme.{0}) (p : X ⟶ S) (n : ℕ) (Y : Fin n → Scheme.{0})
    (π : ∀ i, Y i ⟶ X) (hsep : IsSeparated p) (hft : LocallyOfFiniteType p)
    (hprop : ∀ i, IsProper (π i ≫ p)) (hcov : ∀ x : X, ∃ i, x ∈ Set.range (π i)) :
    IsProper p := by
  have huc : UniversallyClosed p := by
    constructor
    intro X' Y' i₁ i₂ f' hpb Z hZ
    have hW : ∀ i, IsPullback (pullback.fst i₁ (π i) ≫ f') (pullback.snd i₁ (π i)) i₂
        (π i ≫ p) := fun i => (IsPullback.of_hasPullback i₁ (π i)).paste_horiz hpb
    have hc : ∀ i, IsClosedMap ⇑(pullback.fst i₁ (π i) ≫ f') := fun i =>
      @UniversallyClosed.universally_isClosedMap _ _ _ (hprop i).toUniversallyClosed
        _ _ _ _ _ (hW i)
    have key : ⇑f' '' Z =
        ⋃ i, ⇑(pullback.fst i₁ (π i) ≫ f') '' (⇑(pullback.fst i₁ (π i)) ⁻¹' Z) := by
      ext y
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, y', hy'⟩ := hcov (i₁ x)
        obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y' hy'.symm
        refine ⟨i, w, ?_, ?_⟩
        · rw [hw]
          exact hx
        · show f' (pullback.fst i₁ (π i) w) = f' x
          rw [hw]
      · rintro ⟨i, w, hw, rfl⟩
        exact ⟨pullback.fst i₁ (π i) w, hw, rfl⟩
    convert isClosed_iUnion_of_finite fun i =>
      hc i _ (hZ.preimage (pullback.fst i₁ (π i)).continuous) using 1
  exact @IsProper.mk _ _ _ hsep huc hft

end GlobalTheory.CompanionTheory.Ar.Approx
