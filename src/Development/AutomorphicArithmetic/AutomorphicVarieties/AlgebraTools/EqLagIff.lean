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

noncomputable section

open Polynomial

namespace UpperTheory.V.AlgebraTools

def lag {R E ι : Type*} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (a : ι → R) (P : E) (i : ι) : E :=
  Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j)) •
    aeval P (∏ j ∈ Finset.univ.erase i, (X - C (a j)))

theorem eq_lag_iff {R E ι : Type*} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (a : ι → R) (P : E) (i : ι) (h : ∀ j, j ≠ i → IsUnit (a i - a j)) (f : E) :
    f = lag a P i ↔ (∏ j ∈ Finset.univ.erase i, (a i - a j)) • f =
      aeval P (∏ j ∈ Finset.univ.erase i, (X - C (a j))) := by
  have hu : IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j)) := by
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one ?_
    intro j hj
    exact h j (Finset.ne_of_mem_erase hj)
  obtain ⟨v, hv⟩ := hu
  unfold lag
  rw [← hv, Ring.inverse_unit, ← Units.smul_def, ← Units.smul_def]
  exact eq_inv_smul_iff

example (R : Type) [CommRing R] (a : Unit → R) (P : R) : lag a P () = 1 := by
  have : (Finset.univ : Finset Unit).erase () = ∅ := rfl
  simp [lag, this]

def pat {ι : Type*} (R : Type*) [CommRing R] (p : ι → ι → Prop) : Submodule R (Matrix ι ι R) where
  carrier := {X | ∀ i j, ¬ p i j → X i j = 0}
  add_mem' := fun hX hY i j h => by simp [hX i j h, hY i j h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c X hX i j h => by simp [hX i j h]

theorem mem_pat {ι R : Type*} [CommRing R] {p : ι → ι → Prop} {X : Matrix ι ι R} :
    X ∈ pat R p ↔ ∀ i j, ¬ p i j → X i j = 0 := Iff.rfl

example {ι R : Type} [CommRing R] : pat R (fun _ _ : ι => True) = ⊤ := by
  ext X; simp [mem_pat]

end UpperTheory.V.AlgebraTools
