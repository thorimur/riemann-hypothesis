import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Rat.Star
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical

namespace AdmissibleUnits

variable {K : Type} [Field K] [NumberField K]

lemma indep (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (a b : ℚ)
    (h : (a : K) + (b : K) * x = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨?_, rfl⟩
    simpa using h
  · exfalso
    have hxq : x = ((-a / b : ℚ) : K) := by
      have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
      push_cast
      field_simp
      linear_combination h
    rw [hxq] at hx
    have h2 : ((-a / b) ^ 2 : ℚ) = -(d : ℚ) := by exact_mod_cast hx
    have hd' : (0 : ℚ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg (-a / b)]

lemma span (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2)
    (y : K) : ∃ a b : ℚ, y = (a : K) + (b : K) * x := by
  have hli : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    apply indep d hd x hx s t
    simpa [Algebra.smul_def, eq_ratCast] using hst
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have := B.sum_repr y
  rw [Fin.sum_univ_two] at this
  simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one] at this
  conv_lhs => rw [← this]
  simp [Algebra.smul_def, eq_ratCast, B]

end AdmissibleUnits

namespace AdmissibleUnits

variable {K : Type} [Field K] [NumberField K]

lemma conj_ne (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (φ : K →+* ℂ) :
    starRingEnd ℂ (φ x) ≠ φ x := by
  intro h
  rw [Complex.conj_eq_iff_re] at h
  have h2 : (φ x) ^ 2 = -(d : ℂ) := by simpa using congrArg φ hx
  rw [← h] at h2
  have h3 : ((φ x).re ^ 2 : ℝ) = -(d : ℝ) := by exact_mod_cast h2
  have : (0 : ℝ) < d := by exact_mod_cast hd
  nlinarith [sq_nonneg (φ x).re]

lemma norm_eq (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) (α : K) : ((Algebra.norm ℚ α : ℚ) : ℝ) = ‖φ α‖ ^ 2 := by
  set ψ : K →ₐ[ℚ] ℂ := φ.toRatAlgHom
  set ψ' : K →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp φ).toRatAlgHom
  have hne : ψ ≠ ψ' := by
    intro h
    have := congrArg (fun f : K →ₐ[ℚ] ℂ => f x) h
    simp only [ψ, ψ', RingHom.toRatAlgHom_apply, RingHom.comp_apply] at this
    exact conj_ne d hd x hx φ this.symm
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = 2 := by rw [AlgHom.card, hK]
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {ψ, ψ'} := by
    symm; apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ α
  rw [huniv, Finset.prod_pair hne] at h
  simp only [ψ, ψ', RingHom.toRatAlgHom_apply, RingHom.comp_apply] at h
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h' : (((Algebra.norm ℚ α : ℚ) : ℝ) : ℂ) = ((‖φ α‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h]; simp
  exact_mod_cast h'

end AdmissibleUnits

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
