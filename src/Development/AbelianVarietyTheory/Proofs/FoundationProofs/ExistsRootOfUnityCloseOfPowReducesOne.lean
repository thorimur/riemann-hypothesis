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
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

open Polynomial

theorem exists_root_of_unity_close_of_pow_close : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K]
    [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 →
    ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := by
  intro Ω K _ _ _ _ _ W x N hN hv
  classical
  set p : Polynomial Ω := X ^ N - C 1 with hp
  have hm : p.Monic := monic_X_pow_sub_C 1 hN.ne'
  have hs := (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
  have hx : x ^ N - 1 = (p.roots.map (fun a => x - algebraMap Ω K a)).prod := by
    have := congrArg (Polynomial.aeval x) hs
    simpa [p, map_multiset_prod, Multiset.map_map, Function.comp_def] using this
  by_contra hcon
  push_neg at hcon
  refine (not_lt.mpr ?_) hv
  rw [hx, map_multiset_prod, Multiset.map_map]
  refine Multiset.one_le_prod_of_one_le ?_
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
  have ha' : a ^ N = 1 := by
    have := (mem_roots hm.ne_zero).mp ha
    simpa [p, sub_eq_zero] using this
  exact hcon a ha'

end GlobalTheory
