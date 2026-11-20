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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def gx (l : Fin n → ℂ) : ℕ → Fin n → ℂ
  | 0, _ => 1
  | k + 1, r => l r * gx l k r - ∑ s ∈ univ.filter (fun s => r < s), gx l k s

def gelfandSeries (l : Fin n → ℂ) : PowerSeries ℂ :=
  1 - ∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹)

def gval (l : Fin n → ℂ) (k : ℕ) : ℂ := PowerSeries.coeff (k + 1) (gelfandSeries l)

def icShift (μ : Fin n → ℝ) : Fin n → ℂ := fun r => ((μ r + ((n : ℝ) - 1) / 2 : ℝ) : ℂ)

def gxSeries (l : Fin n → ℂ) (r : Fin n) : PowerSeries ℂ := PowerSeries.mk fun k => gx l k r

theorem gxSeries_mul (l : Fin n → ℂ) (r : Fin n) :
    gxSeries l r * (1 - PowerSeries.C (l r) * PowerSeries.X) =
      1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s => r < s), gxSeries l s := by
  ext k
  rcases k with _ | k
  · simp [gxSeries, gx]
  · rw [show gxSeries l r * (1 - PowerSeries.C (l r) * PowerSeries.X) =
        gxSeries l r - PowerSeries.C (l r) * (gxSeries l r * PowerSeries.X) by ring,
      map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, map_sub,
      PowerSeries.coeff_succ_X_mul, map_sum]
    simp [gxSeries, gx, PowerSeries.coeff_one]

theorem oneSubCX_const_ne (a : ℂ) : PowerSeries.constantCoeff (1 - PowerSeries.C a * PowerSeries.X) ≠ 0 := by
  simp

theorem gxSeries_eq (l : Fin n → ℂ) (r : Fin n) :
    gxSeries l r = (1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s => r < s), gxSeries l s) *
      (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹ := by
  rw [← gxSeries_mul, mul_assoc, PowerSeries.mul_inv_cancel _ (oneSubCX_const_ne _), mul_one]

theorem gxSeries_tele (l : Fin n → ℂ) (d : ℕ) : ∀ r : ℕ, n - r = d →
    1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s : Fin n => r ≤ s.val), gxSeries l s =
      ∏ s ∈ univ.filter (fun s : Fin n => r ≤ s.val),
        (1 - PowerSeries.X * (1 - PowerSeries.C (l s) * PowerSeries.X)⁻¹) := by
  induction d with
  | zero =>
    intro r hr
    have : univ.filter (fun s : Fin n => r ≤ s.val) = ∅ := by
      ext s; simp; omega
    simp [this]
  | succ d ih =>
    intro r hr
    have hrn : r < n := by omega
    have hins : univ.filter (fun s : Fin n => r ≤ s.val) =
        insert ⟨r, hrn⟩ (univ.filter (fun s : Fin n => r + 1 ≤ s.val)) := by
      ext s; simp [Fin.ext_iff]; omega
    have hgt : univ.filter (fun s : Fin n => (⟨r, hrn⟩ : Fin n) < s) =
        univ.filter (fun s : Fin n => r + 1 ≤ s.val) := by
      ext s; simp only [mem_filter, mem_univ, true_and, Fin.lt_def]; omega
    have hnot : (⟨r, hrn⟩ : Fin n) ∉ univ.filter (fun s : Fin n => r + 1 ≤ s.val) := by simp
    rw [hins, sum_insert hnot, prod_insert hnot, ← ih (r + 1) (by omega), gxSeries_eq l ⟨r, hrn⟩,
      hgt]
    ring

theorem gelfandSeries_eq (l : Fin n → ℂ) :
    gelfandSeries l = PowerSeries.X * ∑ r, gxSeries l r := by
  have h := gxSeries_tele l n 0 (by simp)
  have e : univ.filter (fun s : Fin n => 0 ≤ s.val) = univ := by ext; simp
  rw [e] at h
  rw [gelfandSeries, ← h]
  ring

theorem sum_gx_eq_gval (l : Fin n → ℂ) (k : ℕ) : ∑ r, gx l k r = gval l k := by
  rw [gval, gelfandSeries_eq, PowerSeries.coeff_succ_X_mul, map_sum]
  simp [gxSeries]

theorem gval_perm (l : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ) : gval (l ∘ σ) k = gval l k := by
  have h : gelfandSeries (l ∘ σ) = gelfandSeries l := by
    simp only [gelfandSeries, Function.comp_apply]
    rw [Equiv.prod_comp σ (fun r => (1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹))]
  rw [gval, gval, h]

end ReciprocityTheory.ChartRestriction.DS
