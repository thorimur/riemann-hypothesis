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

namespace MultisetMapEqExistsEquivPerm

private lemma card_fiber {α : Type*} [DecidableEq α] {l : ℕ} (x : Fin l → α) (v : α) :
    Fintype.card {a : Fin l // x a = v} =
      (Multiset.map x Finset.univ.val).countP (fun b => b = v) := by
  rw [Multiset.countP_map, Fintype.card_subtype]
  rfl

end MultisetMapEqExistsEquivPerm

theorem UpperTheory.Reformulated.B.Yhb6.main.{u_1} :
    ∀ {α : Type u_1} {l : ℕ} {x y : Fin l → α},
      Multiset.map y Finset.univ.val = Multiset.map x Finset.univ.val →
        ∃ (e : Equiv.Perm (Fin l)), ∀ (a : Fin l), y a = x ((e : Fin l → Fin l) a) := by
  intro α l x y h
  classical
  have hc : ∀ v : α, Fintype.card {a : Fin l // y a = v} = Fintype.card {a : Fin l // x a = v} := by
    intro v
    convert (MultisetMapEqExistsEquivPerm.card_fiber y v).trans
      ((congrArg (fun m => Multiset.countP (fun b => b = v) m) h).trans (MultisetMapEqExistsEquivPerm.card_fiber x v).symm)
  let E : ∀ v : α, {a : Fin l // y a = v} ≃ {a : Fin l // x a = v} :=
    fun v => Fintype.equivOfCardEq (hc v)
  refine ⟨Equiv.ofFiberEquiv E, fun a => ?_⟩
  exact (Equiv.ofFiberEquiv_map E a).symm
