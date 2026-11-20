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
import Std.Tactic.BVDecide.Normalize.Prop

namespace GlobalTheory.HarmLine

def zR (m n p : ℕ) : Fin (min p m) × Fin n → Fin m × Fin n :=
  fun u => (⟨u.1, lt_of_lt_of_le u.1.2 (min_le_right _ _)⟩, u.2)

def yR (m n p : ℕ) : Fin (m - p) × Fin n → Fin m × Fin n :=
  fun u => (⟨m - 1 - u.1, by have := u.1.2; omega⟩, u.2)

theorem zR_inj (m n p : ℕ) : Function.Injective (zR m n p) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [zR, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) h.2

theorem yR_inj (m n p : ℕ) : Function.Injective (yR m n p) := by
  rintro ⟨⟨a, ha⟩, b⟩ ⟨⟨c, hc⟩, d⟩ h
  simp only [yR, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Prod.ext (Fin.ext (by simp only; omega)) h.2

theorem zR_ne_yR (m n p : ℕ) (u : Fin (min p m) × Fin n) (v : Fin (m - p) × Fin n) : zR m n p u ≠ yR m n p v := by
  intro h
  simp only [zR, yR, Prod.mk.injEq, Fin.mk.injEq] at h
  have := u.1.2; have := v.1.2
  have := min_le_left p m
  omega

theorem zR_yR_cover (m n p : ℕ) (s : Fin m × Fin n) : (∃ u, zR m n p u = s) ∨ ∃ v, yR m n p v = s := by
  rcases s with ⟨i, a⟩
  by_cases h : (i : ℕ) < p
  · left
    exact ⟨(⟨i, lt_min h i.2⟩, a), rfl⟩
  · right
    refine ⟨(⟨m - 1 - i, by have := i.2; omega⟩, a), ?_⟩
    simp only [yR, Prod.mk.injEq, and_true]
    ext
    simp only
    have := i.2
    omega

end GlobalTheory.HarmLine
