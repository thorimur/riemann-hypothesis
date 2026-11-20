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
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem exists_lift_pow {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M] (l : ℕ) [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    (hirr : Irreducible (cyclotomic l K)) {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (τ : (ZMod l)ˣ) :
    ∃ g : Gal(M/ℚ), AlgEquiv.restrictNormal g K = σ ∧ g ζ = ζ ^ (τ : ZMod l).val := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero l := ⟨hl.ne'⟩
  obtain ⟨g₀, hg₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) M σ
  have hg₀ζ : IsPrimitiveRoot (g₀ ζ) l := hζ.map_of_injective g₀.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hg₀ζ.pow_eq_one
  have hcop : i.Coprime l := (hζ.pow_iff_coprime hl i).mp (hi ▸ hg₀ζ)
  set u : (ZMod l)ˣ := ZMod.unitOfCoprime i hcop with hu
  set t : (ZMod l)ˣ := τ * u⁻¹ with ht
  set h : M ≃ₐ[K] M := (IsCyclotomicExtension.autEquivPow M hirr).symm t with hh
  have hz := IsCyclotomicExtension.zeta_spec l K M
  have hhz : h (IsCyclotomicExtension.zeta l K M) = (IsCyclotomicExtension.zeta l K M) ^ (t : ZMod l).val := by
    have h1 := hz.autToPow_spec K h
    have h2 : hz.autToPow K h = t := by
      have := (IsCyclotomicExtension.autEquivPow M hirr).apply_symm_apply t
      exact this
    rw [← h1, h2]
  obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hhζ : h ζ = ζ ^ (t : ZMod l).val := by
    rw [← ha, map_pow, hhz, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨h.restrictScalars ℚ * g₀, ?_, ?_⟩
  · have h1 : AlgEquiv.restrictNormal (h.restrictScalars ℚ) K = 1 := by
      ext x
      have e := AlgEquiv.restrictNormal_commutes (h.restrictScalars ℚ : M ≃ₐ[ℚ] M) K x
      have e2 : (h.restrictScalars ℚ) (algebraMap K M x) = algebraMap K M x := h.commutes x
      rw [e2] at e
      exact (algebraMap K M).injective e
    have h2 : AlgEquiv.restrictNormal (h.restrictScalars ℚ * g₀) K =
        AlgEquiv.restrictNormal (h.restrictScalars ℚ) K * AlgEquiv.restrictNormal g₀ K :=
      map_mul (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := M) K) _ _
    rw [h2, h1, one_mul]
    exact hg₀
  · show h (g₀ ζ) = _
    rw [← hi, map_pow, hhζ, ← pow_mul]
    rw [← pow_mod_orderOf, ← hζ.eq_orderOf, ← pow_mod_orderOf ζ (τ : ZMod l).val, ← hζ.eq_orderOf]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have : ((u : (ZMod l)ˣ) : ZMod l) = (i : ZMod l) := rfl
    rw [← this]
    rw [← Units.val_mul, ht, inv_mul_cancel_right]

end ReciprocityTheory.Cheb
