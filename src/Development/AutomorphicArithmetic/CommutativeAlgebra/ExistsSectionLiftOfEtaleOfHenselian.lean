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
import Mathlib.RingTheory.Unramified.LocalStructure
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

noncomputable section
open IsLocalRing UpperTheory.Et

theorem UpperTheory.exists_section_lift_of_etale_of_henselian :
    ∀ (A E : Type) [CommRing A] [HenselianLocalRing A] [CommRing E] [Algebra A E] [Algebra.Etale A E] (π : E →ₐ[A] ResidueField A), ∃ σ : E →ₐ[A] A, ∀ x, residue A (σ x) = π x := by
  intro A E _ _ _ _ _ π
  classical
  let Q : Ideal E := RingHom.ker π
  haveI : Q.IsPrime := RingHom.ker_isPrime π
  obtain ⟨f, hfQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  obtain ⟨P⟩ := hstd.nonempty_standardEtalePresentation
  have hunit : ∀ y : Submonoid.powers f, IsUnit (π y) := by
    rintro ⟨_, n, rfl⟩
    simp only [map_pow]
    exact (isUnit_iff_ne_zero.mpr fun h => hfQ (RingHom.mem_ker.mpr h)).pow n
  let πf : Localization.Away f →ₐ[A] ResidueField A := IsLocalization.liftAlgHom (M := Submonoid.powers f) hunit
  let ι : E →ₐ[A] Localization.Away f := IsScalarTower.toAlgHom A E _
  have hπ : ∀ x, πf (ι x) = π x := fun x => by
    simp [πf, ι]
  let τ : P.Ring →ₐ[A] ResidueField A := πf.comp P.equivRing.symm.toAlgHom
  have hx : P.HasMap (τ P.X) := StandardEtalePair.hasMap_X.map τ
  have key : ∀ b : A, residue A b = τ P.X → ∀ p : Polynomial A, residue A (p.eval b) = Polynomial.aeval (τ P.X) p := by
    intro b hb p
    rw [← hb, ← ResidueField.algebraMap_eq, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (τ P.X)
  have h1 : P.f.eval a₀ ∈ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, key a₀ ha₀]
    exact hx.1
  have h2 : IsUnit (P.f.derivative.eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key a₀ ha₀]
    exact hx.isUnit_derivative_f.ne_zero
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀ h1 h2
  have hra : residue A a = τ P.X := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at ham
    rw [ham, ha₀]
  have hA : P.HasMap a := by
    refine ⟨by rw [Polynomial.coe_aeval_eq_eval]; exact ha, ?_⟩
    rw [Polynomial.coe_aeval_eq_eval, ← IsLocalRing.residue_ne_zero_iff_isUnit, key a hra]
    exact hx.2.ne_zero
  let ρ : A →ₐ[A] ResidueField A := IsScalarTower.toAlgHom A A (ResidueField A)
  have hρ : ρ.comp (P.lift a hA) = τ := by
    apply StandardEtalePair.hom_ext
    simp [ρ, hra, ResidueField.algebraMap_eq]
  refine ⟨(P.lift a hA).comp (P.equivRing.toAlgHom.comp ι), fun x => ?_⟩
  have := congrArg (fun φ => φ (P.equivRing (ι x))) hρ
  simp only [AlgHom.comp_apply, ρ, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq, τ, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.symm_apply_apply] at this
  simpa [hπ] using this

end
