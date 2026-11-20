import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

namespace GlobalTheory.InverseEntryDifferentiability

open Matrix

theorem prod_differentiableAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {ι : Type} [DecidableEq ι] (h : ι → F → ℂ) (x : F) (s : Finset ι)
    (hh : ∀ i ∈ s, DifferentiableAt ℂ (h i) x) :
    DifferentiableAt ℂ (fun y : F => ∏ i ∈ s, h i y) x := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiableAt_const _
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hh a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hh i (Finset.mem_insert_of_mem hi))

theorem det_differentiableAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {n : Type} [Fintype n] [DecidableEq n] (g : F → Matrix n n ℂ) (x : F)
    (hg : ∀ i j : n, DifferentiableAt ℂ (fun y : F => g y i j) x) :
    DifferentiableAt ℂ (fun y : F => (g y).det) x := by
  simp_rw [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.const_mul
  exact prod_differentiableAt (fun i y => g y (σ i) i) x Finset.univ (fun i _ => hg (σ i) i)

theorem adjugate_differentiableAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {n : Type} [Fintype n] [DecidableEq n] (g : F → Matrix n n ℂ) (x : F)
    (hg : ∀ i j : n, DifferentiableAt ℂ (fun y : F => g y i j) x) (i j : n) :
    DifferentiableAt ℂ (fun y : F => (g y).adjugate i j) x := by
  simp_rw [Matrix.adjugate_apply]
  apply det_differentiableAt (fun y => (g y).updateRow j (Pi.single i 1)) x
  intro k l
  by_cases h : k = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact differentiableAt_const _
  · simp only [Matrix.updateRow_ne h]
    exact hg k l

theorem inv_entry_differentiableAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {n : Type} [Fintype n] [DecidableEq n] (f : F → Matrix n n ℂ) (x : F)
    (hf : ∀ i j : n, DifferentiableAt ℂ (fun y : F => f y i j) x) (hu : IsUnit (f x))
    (i j : n) : DifferentiableAt ℂ (fun y : F => (f y)⁻¹ i j) x := by
  have hdet : (f x).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  have key : (fun y : F => (f y)⁻¹ i j) = fun y => ((f y).det)⁻¹ * (f y).adjugate i j := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  rw [key]
  exact ((det_differentiableAt f x hf).inv hdet).mul (adjugate_differentiableAt f x hf i j)

theorem main : ∀ {F : Type} [inst : NormedAddCommGroup F] [inst_1 : NormedSpace ℂ F] {n : Type}
    [inst_2 : Fintype n] [inst_3 : DecidableEq n] (f : F → Matrix n n ℂ) (x : F),
    (∀ (i j : n), DifferentiableAt ℂ (fun (y : F) ↦ f y i j) x) → IsUnit (f x) →
    ∀ (i j : n), DifferentiableAt ℂ (fun (y : F) ↦ (f y)⁻¹ i j) x := by
  intro F _ _ n _ _ f x hf hu i j
  exact inv_entry_differentiableAt f x hf hu i j

end GlobalTheory.InverseEntryDifferentiability
