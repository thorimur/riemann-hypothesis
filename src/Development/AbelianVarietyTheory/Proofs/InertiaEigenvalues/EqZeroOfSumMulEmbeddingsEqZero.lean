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
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

open Module in

theorem eq_zero_of_sum_mul_embeddings_eq_zero (F Ω L : Type) [Field F] [CharZero F] [Field Ω]
    [IsAlgClosed Ω] [Algebra F Ω] [Field L] [Algebra F L] [FiniteDimensional F L] (m : ℕ)
    (e : Fin m → Ω) (he : LinearIndependent F e) (_halg : ∀ t, IsAlgebraic F (e t))
    (a : Fin m → L) (h : ∀ σ : L →ₐ[F] Ω, ∑ t, e t * σ (a t) = 0) : a = 0 := by
  classical
  let b := Module.finBasis F L
  let ε : Fin (Module.finrank F L) ≃ (L →ₐ[F] Ω) :=
    Fintype.equivOfCardEq (by rw [AlgHom.card F L Ω, Fintype.card_fin])
  let E := Algebra.embeddingsMatrixReindex F Ω b ε
  have hE : E.det ≠ 0 := by
    intro h0
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two F Ω b ε
    rw [show (Algebra.embeddingsMatrixReindex F Ω b ε).det = 0 from h0] at h1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
    exact Algebra.discr_not_zero_of_basis F b ((map_eq_zero _).mp h1)
  have hEa : ∀ i k, E i k = ε k (b i) := by
    intro i k
    simp [E, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  let v : Fin (Module.finrank F L) → Ω := fun i => ∑ t, (b.repr (a t) i) • e t
  have hv : Matrix.vecMul v E = 0 := by
    funext k
    rw [Matrix.vecMul, dotProduct]
    simp only [Pi.zero_apply, hEa, v]
    have hk := h (ε k)
    rw [← hk]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    conv_rhs => rw [← b.sum_repr (a t), map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, Algebra.smul_def, Algebra.smul_def]
    ring
  have hv0 : v = 0 := Matrix.eq_zero_of_vecMul_eq_zero hE hv
  have hc : ∀ t i, b.repr (a t) i = 0 := by
    intro t i
    have := congrFun hv0 i
    exact (Fintype.linearIndependent_iff.mp he) (fun t => b.repr (a t) i) this t
  funext t
  rw [Pi.zero_apply, ← b.sum_repr (a t)]
  simp [hc]

end GlobalTheory
