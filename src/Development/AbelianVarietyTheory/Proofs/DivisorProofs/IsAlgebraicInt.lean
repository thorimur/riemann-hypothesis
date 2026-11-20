import Mathlib.Algebra.Module.Lattice
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

namespace GlobalTheory.AlgebraicIntegerMultiple

open NumberField

theorem isAlgebraic_int {E : Type} [Field E] [NumberField E] (c : E) : IsAlgebraic ℤ c := by
  have h : IsIntegral ℚ c := Algebra.IsIntegral.isIntegral c
  exact (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 h.isAlgebraic

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {d : ℕ}
    {L : Submodule (RingOfIntegers E) (Fin d → E)}
    (hL : Submodule.IsLattice E L) (w : Fin d → E) :
    ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin d → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := mul_smul a b y
    rw [smul_add, h1, h2]
    exact L.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨N, hN, hNx⟩ := hx
    obtain ⟨y, hy, hint⟩ := (isAlgebraic_int c).exists_integral_multiple
    let a : RingOfIntegers E := ⟨y • c, hint⟩
    refine ⟨y * N, mul_ne_zero hy hN, ?_⟩
    have key : (y * N) • (c • x) = a • (N • x) := by
      rw [← algebraMap_smul E a (N • x)]
      ext i
      simp [a, Pi.smul_apply, zsmul_eq_mul]
      ring
    rw [key]
    exact L.smul_mem a hNx

end GlobalTheory.AlgebraicIntegerMultiple
