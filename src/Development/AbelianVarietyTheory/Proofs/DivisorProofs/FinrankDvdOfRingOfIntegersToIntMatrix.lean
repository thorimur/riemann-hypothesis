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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open NumberField

namespace GlobalTheory

theorem finrank_dvd_of_ringOfIntegers_to_matrix (E : Type) [Field E] [NumberField E] {r : ℕ}
    (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) : ∃ s : ℕ, r = s * Module.finrank ℚ E := by
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  let g : 𝓞 E →+* Matrix (Fin r) (Fin r) ℚ := (Int.castRingHom ℚ).mapMatrix.comp ρ
  let S : Subalgebra ℚ (Matrix (Fin r) (Fin r) ℚ) := Algebra.adjoin ℚ (Set.range g)
  letI : CommRing S := Algebra.adjoinCommRingOfComm ℚ (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, mul_comm, map_mul])
  let g₁ : 𝓞 E →+* S := g.codRestrict S (fun a => Algebra.subset_adjoin ⟨a, rfl⟩)
  have hg : ∀ y : Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ), IsUnit (g₁ y) := by
    rintro ⟨_, m, hm, rfl⟩
    have hm0 : (m : ℚ) ≠ 0 := by
      exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.mp hm
    have : g₁ (algebraMap ℤ (𝓞 E) m) = algebraMap ℚ S (m : ℚ) := by
      apply Subtype.ext
      simp [g₁, g, map_intCast]
    rw [this]
    exact (IsUnit.mk0 _ hm0).map _
  let ρ' : E →+* Matrix (Fin r) (Fin r) ℚ := S.val.toRingHom.comp (IsLocalization.lift hg)
  letI : Module E (Fin r → ℚ) :=
    Module.compHom (Fin r → ℚ)
      ((Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp ρ')
  have hq : ρ'.comp (algebraMap ℚ E) = algebraMap ℚ (Matrix (Fin r) (Fin r) ℚ) := RingHom.ext_rat _ _
  haveI : IsScalarTower ℚ E (Fin r → ℚ) := by
    refine ⟨fun q e v => ?_⟩
    show Matrix.toLin' (ρ' (q • e)) v = q • Matrix.toLin' (ρ' e) v
    rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, hq, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, map_smul]
    rfl
  refine ⟨Module.finrank E (Fin r → ℚ), ?_⟩
  have := Module.finrank_mul_finrank ℚ E (Fin r → ℚ)
  rw [Module.finrank_fin_fun] at this
  rw [mul_comm] at this
  exact this.symm

end GlobalTheory
