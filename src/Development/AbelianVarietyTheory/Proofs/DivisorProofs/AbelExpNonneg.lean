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

namespace GlobalTheory.FlagZ

def abelExp {ι : Type} {N : ℕ} (lam : ι → Fin N → ℤ) (x : ι × Fin (N + 1)) : ℤ :=
  if h : 0 < (x.2 : ℕ) ∧ (x.2 : ℕ) < N then
    lam x.1 ⟨(x.2 : ℕ) - 1, by omega⟩ - lam x.1 ⟨x.2, h.2⟩
  else 0

theorem abelExp_nonneg {ι : Type} {N : ℕ} (lam : ι → Fin N → ℤ)
    (hlam : ∀ τ (a b : Fin N), a ≤ b → lam τ b ≤ lam τ a) (x : ι × Fin (N + 1)) : 0 ≤ abelExp lam x := by
  unfold abelExp
  split_ifs with h
  · exact sub_nonneg.2 (hlam _ _ _ (Fin.mk_le_mk.2 (Nat.sub_le _ _)))
  · exact le_rfl

end GlobalTheory.FlagZ
