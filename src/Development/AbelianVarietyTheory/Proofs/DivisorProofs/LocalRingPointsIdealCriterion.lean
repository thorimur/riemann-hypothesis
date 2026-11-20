import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
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
import Mathlib.Tactic.ENatToNat
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem exists_ideal_factor_closedImmersion_iff (A : Type) [CommRing A] (X Y : Scheme.{0})
    (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X) [IsClosedImmersion j] :
    ∃ I : Ideal A, ∀ (R : Type) [CommRing R] (ψ : A →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔
        I ≤ RingHom.ker ψ := by
  obtain ⟨I, e, hf⟩ := (IsClosedImmersion.Spec_iff (f := pullback.snd j a)).mp inferInstance
  refine ⟨I, fun R _ ψ => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    let z : Spec (CommRingCat.of R) ⟶ pullback j a := pullback.lift y (Spec.map (CommRingCat.ofHom ψ)) hy
    have hz : z ≫ pullback.snd j a = Spec.map (CommRingCat.ofHom ψ) := pullback.lift_snd _ _ _
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (z ≫ e.hom)
    have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ χ) = Spec.map (CommRingCat.ofHom ψ) := by
      rw [Spec.map_comp, hχ, Category.assoc, ← hf, hz]
    have h2 := Spec.map_injective h1
    intro x hx
    have := congrArg (fun g => g.hom x) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this
    rw [RingHom.mem_ker, ← this, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro h
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun x hx => h hx))) ≫ e.inv ≫ pullback.fst j a, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition, hf, Category.assoc, Iso.inv_hom_id_assoc,
      ← Spec.map_comp_assoc]
    congr 2

theorem factor_closedImmersion_iff_of_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (X Y : Scheme.{0}) (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X), IsClosedImmersion j → ∀ J : Ideal A, (∀ (R : Type) [CommRing R] [IsLocalRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ) → ∀ (R : Type) [CommRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ := by
  intro A _ _ X Y a j hj J H
  obtain ⟨I, hI⟩ := exists_ideal_factor_closedImmersion_iff A X Y a j
  have key : ∀ (K : Ideal A), K ≠ ⊤ → (I ≤ K ↔ J ≤ K) := by
    intro K hK
    haveI : Nontrivial (A ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hK
    haveI : IsLocalRing (A ⧸ K) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have := (hI (A ⧸ K) (Ideal.Quotient.mk K)).symm.trans (H (A ⧸ K) (Ideal.Quotient.mk K))
    simpa [Ideal.mk_ker] using this
  have hIJ : I = J := by
    apply le_antisymm
    · by_cases hJ : J = ⊤
      · rw [hJ]; exact le_top
      · exact (key J hJ).mpr le_rfl
    · by_cases hI' : I = ⊤
      · rw [hI']; exact le_top
      · exact (key I hI').mp le_rfl
  intro R _ ψ
  rw [← hIJ]
  exact hI R ψ

end GlobalTheory
