import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init
open NumberField Matrix

namespace GlobalTheory.SylvesterInertia

theorem re_quad_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (u : Fin n → ℂ) :
    (star u ⬝ᵥ M *ᵥ u).re = ∑ i, hM.eigenvalues i * Complex.normSq
      ((star (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ u) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hD : star U * M * U = diagonal (RCLike.ofReal ∘ hM.eigenvalues) := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, hU] using this
  set y := star U *ᵥ u with hy
  have hu : u = U *ᵥ y := by
    rw [hy, mulVec_mulVec, hU, Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2, one_mulVec]
  have h1 : star u ⬝ᵥ M *ᵥ u = star y ⬝ᵥ (star U * M * U) *ᵥ y := by
    conv_lhs => rw [hu]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, star_eq_conjTranspose, Matrix.mul_assoc]
  rw [h1, hD, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  have e1 : ((RCLike.ofReal (hM.eigenvalues i) : ℂ)).re = hM.eigenvalues i := by simp
  have e2 : ((RCLike.ofReal (hM.eigenvalues i) : ℂ)).im = 0 := by simp
  simp only [e1, e2]
  ring

theorem finrank_le_card_of_vanish {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (P : Submodule ℂ (Fin n → ℂ))
    (s : Fin n → Prop) [DecidablePred s]
    (h : ∀ u ∈ P, (∀ i, s i → (U *ᵥ u) i = 0) → u = 0) :
    Module.finrank ℂ P ≤ Fintype.card {i // s i} := by
  let f : P →ₗ[ℂ] ({i // s i} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // s i} → Fin n)) ∘ₗ (Matrix.mulVecLin U) ∘ₗ P.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have := h u u.2 (fun i hi => by
      have := congrFun hu ⟨i, hi⟩
      simpa [f, LinearMap.funLeft_apply] using this)
    exact Subtype.ext this
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa using this

end GlobalTheory.SylvesterInertia
