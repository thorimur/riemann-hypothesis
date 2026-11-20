import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.NumberTheory.Padics.Complex
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
open NumberField

noncomputable section
namespace GlobalTheory

theorem norm_ratCast_padicComplex (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ‖(q : ℂ_[p])‖ = padicNorm p q := by
  have h := PadicComplex.norm_extends' p (q : ℚ_[p])
  rw [Padic.eq_padicNorm] at h
  rw [← h]
  congr 1
  rw [map_ratCast]
  exact (map_ratCast (UniformSpace.Completion.coeRingHom : PadicAlgCl p →+* ℂ_[p]) q).symm

theorem sum_log_norm_embeddings_padicComplex (K : Type) [Field K] [NumberField K] (p : ℕ)
    [Fact p.Prime] (a : K) (ha : a ≠ 0) :
    ∑ᶠ j : K →+* ℂ_[p], Real.log ‖j a‖ = -((padicValRat p (Algebra.norm ℚ a) : ℝ) * Real.log p) := by
  classical
  have hN : Algebra.norm ℚ a ≠ 0 := (Algebra.norm_ne_zero_iff).2 ha
  rw [finsum_eq_sum_of_fintype]
  have hsum : ∑ j : K →+* ℂ_[p], Real.log ‖j a‖ = ∑ σ : K →ₐ[ℚ] ℂ_[p], Real.log ‖σ a‖ := by
    refine Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ_[p]) _ _ (fun j => rfl)
  rw [hsum, ← Real.log_prod (fun σ _ => (norm_ne_zero_iff.2 ((map_ne_zero σ).2 ha))), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ_[p] a]
  have : (algebraMap ℚ ℂ_[p]) (Algebra.norm ℚ a) = ((Algebra.norm ℚ a : ℚ) : ℂ_[p]) := by simp
  rw [this, norm_ratCast_padicComplex, padicNorm.eq_zpow_of_nonzero hN]
  push_cast
  rw [Real.log_zpow]
  push_cast
  ring

end GlobalTheory
