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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

open Matrix

namespace GlobalTheory.CompanionTheory.Metric.Telescope

theorem fin_iic_telescope : ∀ (N : ℕ) (M : Type) [AddCommGroup M] (f : Fin N → M) (i : Fin N),
    f i = -∑ k ∈ Finset.Iic i, (if h : (k : ℕ) = 0 then -f k else
      f ⟨(k : ℕ) - 1, by have := k.2; omega⟩ - f k) := by
  intro N M _ f i
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero =>
    have hset : Finset.Iic (⟨0, hn⟩ : Fin N) = {⟨0, hn⟩} := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    rw [hset, Finset.sum_singleton, dif_pos rfl, neg_neg]
  | succ n ih =>
    have hn' : n < N := by omega
    have hset : Finset.Iic (⟨n + 1, hn⟩ : Fin N) = insert ⟨n + 1, hn⟩ (Finset.Iic ⟨n, hn'⟩) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    have hnot : (⟨n + 1, hn⟩ : Fin N) ∉ Finset.Iic ⟨n, hn'⟩ := by
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val, not_le]
      omega
    have hs := (neg_eq_iff_eq_neg.mpr (ih hn')).symm
    rw [hset, Finset.sum_insert hnot, dif_neg (by simp), hs]
    have e : ∀ p, f ⟨(⟨n + 1, hn⟩ : Fin N).val - 1, p⟩ = f ⟨n, hn'⟩ :=
      fun p => congrArg f (Fin.ext (by simp))
    rw [e]
    abel

end GlobalTheory.CompanionTheory.Metric.Telescope
