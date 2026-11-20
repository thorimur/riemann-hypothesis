import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem sum_log_embedding_add_finsum_log_adicAbv_eq_zero
    (F : Type) [Field F] [NumberField F] (N : F) (hN : N ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)).Finite ∧
      (∑ σ : F →+* ℂ, Real.log ‖σ N‖) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 F),
          Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) = 0 := by
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => NumberField.HeightOneSpectrum.adicAbv F v N) =
      (fun w : FinitePlace F => w N) ∘ (FinitePlace.equivHeightOneSpectrum (K := F)).symm := by
    funext v
    simp only [Function.comp, FinitePlace.equivHeightOneSpectrum_symm_apply,
      FinitePlace.norm_embedding]
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      NumberField.HeightOneSpectrum.adicAbv F v N).Finite := by
    rw [hfun, Function.mulSupport_comp_eq_preimage]
    exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
      (FinitePlace.hasFiniteMulSupport hN)
  have hpos : ∀ v : HeightOneSpectrum (𝓞 F), 0 < NumberField.HeightOneSpectrum.adicAbv F v N :=
    fun v => (NumberField.HeightOneSpectrum.adicAbv F v).pos hN
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v N =
      ((|Algebra.norm ℚ N|⁻¹ : ℚ) : ℝ) := by
    rw [← FinitePlace.prod_eq_inv_abs_norm hN,
      ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
    exact congrArg finprod hfun
  have hsub : (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)) ⊆ hfin.toFinset := by
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h
    exact hv (by simp only [h, Real.log_one])
  refine ⟨hfin.toFinset.finite_toSet.subset hsub, ?_⟩
  have h1 : ∑ᶠ v : HeightOneSpectrum (𝓞 F),
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) =
      - Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _ hsub, ← Real.log_prod (fun v _ => (hpos v).ne'),
      ← finprod_eq_prod_of_mulSupport_subset _ (by simp), hprod, Rat.cast_inv, Real.log_inv]
  have h2 : ∑ σ : F →+* ℂ, Real.log ‖σ N‖ = Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
    have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ N)
    simp only [norm_prod] at h
    rw [← Real.log_prod (fun σ _ => by simpa using hN)]
    congr 1
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun σ : F →+* ℂ => ‖σ N‖)
      (fun σ : F →ₐ[ℚ] ℂ => ‖σ N‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
    simp [← Complex.norm_ratCast]
  rw [h1, h2, add_neg_cancel]

end GlobalTheory
