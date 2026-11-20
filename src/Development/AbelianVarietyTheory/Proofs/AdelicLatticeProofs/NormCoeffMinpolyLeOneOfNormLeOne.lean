import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem norm_coeff_minpoly_le_one_of_norm_le_one (K : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) (h : ‖Algebra.norm K x‖ ≤ 1) (n : ℕ) :
    ‖(minpoly K x).coeff n‖ ≤ 1 := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖(minpoly K x).coeff 0‖ ≤ 1 := by
    rw [Algebra.norm_eq_norm_adjoin K x, ← IntermediateField.adjoin.powerBasis_gen hx,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
      IntermediateField.minpoly_gen, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Module.finrank_pos).ne').1 h
  have h1 : spectralNorm K L x ≤ 1 := by
    rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L x]
    exact Real.rpow_le_one (norm_nonneg _) h0 (by positivity)
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h1
  exact h1 n

theorem isIntegral_iff_valued_norm_le_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (L : Type) [Field L] [Algebra (v.adicCompletion F) L]
    [FiniteDimensional (v.adicCompletion F) L] [Algebra (v.adicCompletionIntegers F) L]
    [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) L] (x : L) :
    IsIntegral (v.adicCompletionIntegers F) x ↔
      Valued.v (Algebra.norm (v.adicCompletion F) x) ≤ 1 := by
  constructor
  · intro h
    have h1 : IsIntegral (v.adicCompletionIntegers F) (Algebra.norm (v.adicCompletion F) x) :=
      Algebra.isIntegral_norm (v.adicCompletion F) h
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := v.adicCompletion F)).1 h1
    rw [← hy]
    exact y.2
  · intro h
    letI : NontriviallyNormedField (v.adicCompletion F) :=
      Valued.toNontriviallyNormedField (v.adicCompletion F) ℤᵐ⁰
    haveI : IsUltrametricDist (v.adicCompletion F) :=
      inferInstanceAs (@IsUltrametricDist (v.adicCompletion F)
        (Valued.toNormedField (v.adicCompletion F) ℤᵐ⁰).toDist)
    have hc : ∀ n, Valued.v ((minpoly (v.adicCompletion F) x).coeff n) ≤ 1 := fun n =>
      Valued.toNormedField.norm_le_one_iff.1
        (norm_coeff_minpoly_le_one_of_norm_le_one (v.adicCompletion F) L x
          (Valued.toNormedField.norm_le_one_iff.2 h) n)
    have hx : IsIntegral (v.adicCompletion F) x := Algebra.IsIntegral.isIntegral x
    have hl : minpoly (v.adicCompletion F) x ∈
        Polynomial.lifts (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (v.adicCompletion F), hq,
      minpoly.aeval]

end GlobalTheory.CNorm
