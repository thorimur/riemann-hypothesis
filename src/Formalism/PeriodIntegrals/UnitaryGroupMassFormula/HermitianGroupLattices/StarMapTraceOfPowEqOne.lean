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
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RepresentationTheory.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace PI.Dv.GLatHermW

open Matrix
open scoped ComplexOrder

theorem star_trace_of_pow_eq_one {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (n : ℕ) (hn : 0 < n) (hA : A ^ n = 1) :
    star A.trace = (A ^ (n - 1)).trace := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set Q : Matrix d d ℂ := ∑ k ∈ Finset.range (m + 1), (A ^ k)ᴴ * A ^ k with hQdef
  have hQpd : Q.PosDef := by
    rw [hQdef, Finset.sum_range_succ']
    simp only [pow_zero, conjTranspose_one, one_mul]
    rw [add_comm]
    exact (PosDef.one).add_posSemidef
      (posSemidef_sum _ fun k _ => posSemidef_conjTranspose_mul_self _)
  have hAQ : Aᴴ * Q * A = Q := by
    rw [hQdef, Finset.mul_sum, Finset.sum_mul]
    have : ∀ k, Aᴴ * ((A ^ k)ᴴ * A ^ k) * A = (A ^ (k + 1))ᴴ * A ^ (k + 1) := by
      intro k
      rw [pow_succ, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    simp only [this]
    have key : ∀ F : ℕ → Matrix d d ℂ, F (m + 1) = F 0 →
        ∑ x ∈ Finset.range (m + 1), F (x + 1) = ∑ x ∈ Finset.range (m + 1), F x := by
      intro F hF
      rw [Finset.sum_range_succ, Finset.sum_range_succ' F, hF]
    exact key (fun k => (A ^ k)ᴴ * A ^ k) (by simp [hA])
  have hAQ' : Aᴴ * Q = Q * A ^ m := by
    have h2 : Aᴴ * Q * A * A ^ m = Q * A ^ m := by rw [hAQ]
    rw [Matrix.mul_assoc, ← pow_succ', hA, Matrix.mul_one] at h2
    exact h2
  have hU : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQpd.isUnit
  have hinv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hU
  have hinv' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hU
  calc star A.trace = (Aᴴ).trace := (trace_conjTranspose A).symm
    _ = (Aᴴ * (Q * Q⁻¹)).trace := by rw [hinv, Matrix.mul_one]
    _ = (Q⁻¹ * (Aᴴ * Q)).trace := by rw [← Matrix.mul_assoc, trace_mul_comm]
    _ = (A ^ m).trace := by rw [hAQ', ← Matrix.mul_assoc, hinv', Matrix.one_mul]

theorem star_map_trace_of_pow_eq_one {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (σ : K →+* ℂ) (f : Module.End K W) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) :
    star (σ (LinearMap.trace K W f)) = σ (LinearMap.trace K W (f ^ (n - 1))) := by
  classical
  let b := Module.finBasis K W
  obtain ⟨A, hAdef⟩ : ∃ A, LinearMap.toMatrix b b f = A := ⟨_, rfl⟩
  have hpow : ∀ k, LinearMap.toMatrix b b (f ^ k) = A ^ k := fun k => by
    rw [← LinearMap.toMatrix_pow, hAdef]
  have hmap : ∀ B : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K,
      σ B.trace = (B.map σ).trace := fun B => AddMonoidHom.map_trace σ B
  have hmp : ∀ k, (A ^ k).map σ = (A.map σ) ^ k := fun k => RingHom.map_pow σ.mapMatrix A k
  rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.trace_eq_matrix_trace K b, hAdef, hpow, hmap,
    hmap, hmp]
  refine star_trace_of_pow_eq_one (A.map σ) n hn ?_
  rw [← hmp, ← hpow, hf, LinearMap.toMatrix_one]
  exact Matrix.map_one σ (map_zero σ) (map_one σ)

theorem star_map_trace_rep {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (σ : K →+* ℂ)
    (τ : Representation K G W) (g : G) :
    star (σ (LinearMap.trace K W (τ g))) = σ (LinearMap.trace K W (τ g⁻¹)) := by
  have hn : 0 < Fintype.card G := Fintype.card_pos
  rw [star_map_trace_of_pow_eq_one σ (τ g) (Fintype.card G) hn
    (by rw [← map_pow, pow_card_eq_one, map_one])]
  congr 2
  rw [← map_pow]
  congr 1
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hn, pow_card_eq_one]

end PI.Dv.GLatHermW
