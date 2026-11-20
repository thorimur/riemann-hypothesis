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

theorem UpperTheory.Reformulated.B.Qg2.near_of_adjoin :
    ∀ {P L : Type} [inst : CommRing P] [inst_1 : CommRing L]
    [inst_2 : Algebra P L] (G : Set L),
    (∀ g ∈ G, IsNilpotent g) →
      ∀ x ∈ Algebra.adjoin P G, ∃ (p : P), IsNilpotent (x - (Algebra.algebraMap P L : P → L) p) := by
  intro P L _ _ _ G hG x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, by simpa using hG y hy⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p + q, ?_⟩
    have h := (Commute.all _ _).isNilpotent_add hp hq
    convert h using 1
    rw [map_add]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p * q, ?_⟩
    rw [← mem_nilradical] at hp hq ⊢
    have h := (nilradical L).add_mem ((nilradical L).mul_mem_right z hp)
      ((nilradical L).mul_mem_left ((Algebra.algebraMap P L : P → L) p) hq)
    convert h using 1
    rw [map_mul]
    ring
