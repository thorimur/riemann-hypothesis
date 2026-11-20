import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace ModelDimension

open MvPolynomial

theorem polynomial_fraction_field_degree : ∀ (κ K L I : Type) [Field κ] [Field K] [Field L] [Algebra K L] (ψ : κ ≃+* K) (T : I → L), AlgebraicIndependent K T → ∃ φ : FractionRing (MvPolynomial I κ) →+* L, (∀ a, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.C a)) = algebraMap K L (ψ a)) ∧ (∀ i, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.X i)) = T i) ∧ (letI := φ.toAlgebra; Module.finrank (FractionRing (MvPolynomial I κ)) L) = Module.finrank (IntermediateField.adjoin K (Set.range T)) L := by
  intro κ K L I _ _ _ _ ψ T hT
  let f : κ →+* L := (algebraMap K L).comp ψ.toRingHom
  let ρ : MvPolynomial I κ →+* L := MvPolynomial.eval₂Hom f T
  have hρ : ∀ p, ρ p = MvPolynomial.aeval T (MvPolynomial.map ψ.toRingHom p) := by
    intro p
    simp [ρ, f, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  have hinj : Function.Injective ρ := by
    intro p q h
    rw [hρ, hρ] at h
    exact MvPolynomial.map_injective _ ψ.injective (hT h)
  let φ : FractionRing (MvPolynomial I κ) →+* L := IsFractionRing.lift hinj
  have hφ : ∀ p, φ (algebraMap (MvPolynomial I κ) _ p) = ρ p := IsFractionRing.lift_algebraMap hinj
  refine ⟨φ, fun a => by rw [hφ]; simp [ρ, f], fun i => by rw [hφ]; simp [ρ], ?_⟩
  let S := IntermediateField.adjoin K (Set.range T)
  have hρS : ∀ p, ρ p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [ρ, f]
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact S.mul_mem hp (by simpa [ρ] using IntermediateField.subset_adjoin K (Set.range T) ⟨i, rfl⟩)
  have hφS : ∀ x, φ x ∈ S := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial I κ) x
    rw [map_div₀, hφ, hφ]
    exact S.div_mem (hρS a) (hρS b)
  have hS : S ≤ φ.fieldRange.toIntermediateField (K := K) (fun k =>
      RingHom.mem_fieldRange.2 ⟨algebraMap _ _ (MvPolynomial.C (ψ.symm k)), by rw [hφ]; simp [ρ, f]⟩) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_fieldRange.2 ⟨algebraMap _ _ (MvPolynomial.X i), by rw [hφ]; simp [ρ]⟩
  let g : FractionRing (MvPolynomial I κ) →+* S := φ.codRestrict S hφS
  have hg : Function.Bijective g := by
    refine ⟨fun x y h => φ.injective (congrArg Subtype.val h), ?_⟩
    rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.1 (hS hs)
    exact ⟨x, Subtype.ext hx⟩
  let _ := φ.toAlgebra
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective g hg) (RingEquiv.refl L)
    (RingHom.ext fun x => rfl)

end ModelDimension
