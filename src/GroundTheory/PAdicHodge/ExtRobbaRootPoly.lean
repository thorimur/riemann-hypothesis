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
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

theorem nnnorm_multiset_sum_le_of_forall {m : Multiset F} {B : NNReal} (h : ∀ x ∈ m, ‖x‖₊ ≤ B) :
    ‖m.sum‖₊ ≤ B := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.sum_cons]
    refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le (h a (Multiset.mem_cons_self _ _))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)))

theorem nnnorm_multiset_prod' (m : Multiset F) : ‖m.prod‖₊ = (m.map fun a => ‖a‖₊).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => rw [Multiset.prod_cons, nnnorm_mul, ih, Multiset.map_cons, Multiset.prod_cons]

variable [IsAlgClosed F]

end GroundTheory.PAdicHodge
