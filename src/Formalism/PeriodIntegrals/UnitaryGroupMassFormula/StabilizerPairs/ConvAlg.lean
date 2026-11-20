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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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

open Matrix

noncomputable section
namespace PI.StabPairs.ConvAlg

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def rhoOf (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ) : Matrix n n ℂ :=
  1 + F * ((W - 1) * ((Fᴴ * H * F)⁻¹ * (Fᴴ * H)))

theorem rhoOf_mul (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (hG : IsUnit (Fᴴ * H * F).det) : rhoOf H F W * F = F * W := by
  have hinv : (Fᴴ * H * F)⁻¹ * (Fᴴ * H * F) = 1 := Matrix.nonsing_inv_mul _ hG
  rw [rhoOf, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc F, Matrix.mul_assoc (W - 1),
    Matrix.mul_assoc (Fᴴ * H * F)⁻¹, hinv, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  abel

theorem rhoOf_mulVec_of_ker (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (v : n → ℂ) (hv : (Fᴴ * H) *ᵥ v = 0) : rhoOf H F W *ᵥ v = v := by
  rw [rhoOf, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hv]
  simp

theorem rhoOf_unitary (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (hH : Hᴴ = H) (hG : IsUnit (Fᴴ * H * F).det) (hW : Wᴴ * (Fᴴ * H * F) * W = Fᴴ * H * F) :
    (rhoOf H F W)ᴴ * H * rhoOf H F W = H := by
  have hGh : (Fᴴ * H * F)ᴴ = Fᴴ * H * F := by
    simp [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc]
  have hinvh : ((Fᴴ * H * F)⁻¹)ᴴ = (Fᴴ * H * F)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGh]
  have hFHh : (Fᴴ * H)ᴴ = H * F := by simp [Matrix.conjTranspose_mul, hH]
  have hGi : (Fᴴ * H * F) * (Fᴴ * H * F)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG
  have hiG : (Fᴴ * H * F)⁻¹ * (Fᴴ * H * F) = 1 := Matrix.nonsing_inv_mul _ hG
  have hKh : ((Fᴴ * H * F)⁻¹ * (Fᴴ * H))ᴴ = H * F * (Fᴴ * H * F)⁻¹ := by
    rw [Matrix.conjTranspose_mul, hinvh, hFHh]
  have e1 : H * F = ((Fᴴ * H * F)⁻¹ * (Fᴴ * H))ᴴ * (Fᴴ * H * F) := by
    rw [hKh, Matrix.mul_assoc, hiG, Matrix.mul_one]
  have e2 : Fᴴ * H = (Fᴴ * H * F) * ((Fᴴ * H * F)⁻¹ * (Fᴴ * H)) := by
    rw [← Matrix.mul_assoc, hGi, Matrix.one_mul]
  unfold rhoOf
  generalize hKd : (Fᴴ * H * F)⁻¹ * (Fᴴ * H) = K at e1 e2 ⊢
  generalize hGd : Fᴴ * H * F = G at e1 e2 hW
  have t3 : Kᴴ * (W - 1)ᴴ * Fᴴ * H * F * (W - 1) * K = Kᴴ * (W - 1)ᴴ * G * (W - 1) * K := by
    rw [← hGd]; simp only [Matrix.mul_assoc]
  have t1 : H * F * (W - 1) * K = Kᴴ * G * (W - 1) * K := by rw [e1]
  have t2 : Kᴴ * (W - 1)ᴴ * Fᴴ * H = Kᴴ * (W - 1)ᴴ * G * K := by
    rw [Matrix.mul_assoc (Kᴴ * (W - 1)ᴴ) Fᴴ H, e2, ← Matrix.mul_assoc]
  have inner : G * (W - 1) + (W - 1)ᴴ * G + (W - 1)ᴴ * G * (W - 1) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    calc G * (W - 1) + (Wᴴ - 1) * G + (Wᴴ - 1) * G * (W - 1) = Wᴴ * G * W - G := by noncomm_ring
      _ = 0 := by rw [hW, sub_self]
  calc (1 + F * ((W - 1) * K))ᴴ * H * (1 + F * ((W - 1) * K))
      = H + H * F * (W - 1) * K + Kᴴ * (W - 1)ᴴ * Fᴴ * H
        + Kᴴ * (W - 1)ᴴ * Fᴴ * H * F * (W - 1) * K := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
        abel
    _ = H + Kᴴ * (G * (W - 1) + (W - 1)ᴴ * G + (W - 1)ᴴ * G * (W - 1)) * K := by
        rw [t3, t1, t2]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
        abel
    _ = H := by rw [inner]; simp

end PI.StabPairs.ConvAlg
