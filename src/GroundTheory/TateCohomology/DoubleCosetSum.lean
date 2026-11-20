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
import Mathlib.GroupTheory.DoubleCoset
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

open Pointwise

namespace GroundTheory.GroupCoh

variable {G : Type*} [Group G] (T S : Subgroup G)

open scoped Classical in

noncomputable instance fintypeDoubleCosetQuotient [Finite G] :
    Fintype (DoubleCoset.Quotient (T : Set G) S) :=
  @Fintype.ofFinite _ (Quotient.finite (DoubleCoset.setoid (T : Set G) S))

lemma mem_inf_conj_smul_iff (g x : G) :
    x ∈ T ⊓ (MulAut.conj g • S : Subgroup G) ↔ x ∈ T ∧ g⁻¹ * x * g ∈ S := by
  rw [Subgroup.mem_inf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv]

def doubleCosetMap (g : G) : T ⧸ (T ⊓ MulAut.conj g • S).subgroupOf T → G ⧸ S :=
  Quotient.map' (fun t => (t : G) * g) fun a b h => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, mem_inf_conj_smul_iff] at h
    rw [QuotientGroup.leftRel_apply]
    have e : ((a : G) * g)⁻¹ * ((b : G) * g) = g⁻¹ * ((a⁻¹ * b : T) : G) * g := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h.2

@[simp]
lemma doubleCosetMap_mk (g : G) (t : T) :
    doubleCosetMap T S g (t : T ⧸ (T ⊓ MulAut.conj g • S).subgroupOf T) = ((t * g : G) : G ⧸ S) :=
  rfl

variable [Fintype G]

end GroundTheory.GroupCoh
