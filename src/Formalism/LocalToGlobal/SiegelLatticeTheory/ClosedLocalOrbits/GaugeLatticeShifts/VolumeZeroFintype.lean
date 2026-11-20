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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Topology.Sheaves.Init

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

def PF (ι : Type*) : Subalgebra ℂ ((ι → ℝ) → ℂ) :=
  (MvPolynomial.aeval (R := ℂ) (fun i (y : ι → ℝ) => (y i : ℂ))).range

theorem PF_eval {ι : Type*} (p : MvPolynomial ι ℂ) (y : ι → ℝ) :
    (MvPolynomial.aeval (R := ℂ) (fun i (y : ι → ℝ) => (y i : ℂ)) p : (ι → ℝ) → ℂ) y =
      MvPolynomial.eval (fun i => (y i : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.aeval_C]
  | add p q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | mul_X p i hp => simp only [map_mul, Pi.mul_apply, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

theorem PF_mem_iff {ι : Type*} {f : (ι → ℝ) → ℂ} :
    f ∈ PF ι ↔ ∃ p : MvPolynomial ι ℂ, ∀ y, f y = MvPolynomial.eval (fun i => (y i : ℂ)) p := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, fun y => PF_eval p y⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, funext fun y => (PF_eval p y).trans (hp y).symm⟩

theorem PF_const {ι : Type*} (a : ℂ) : (fun _ : ι → ℝ => a) ∈ PF ι :=
  PF_mem_iff.2 ⟨MvPolynomial.C a, fun y => by simp⟩

theorem PF_conj {ι : Type*} {f : (ι → ℝ) → ℂ} (hf : f ∈ PF ι) : (fun y => conj (f y)) ∈ PF ι := by
  obtain ⟨p, hp⟩ := PF_mem_iff.1 hf
  refine PF_mem_iff.2 ⟨MvPolynomial.map (starRingEnd ℂ) p, fun y => ?_⟩
  rw [hp, MvPolynomial.eval_map]
  show starRingEnd ℂ (MvPolynomial.eval₂ (RingHom.id ℂ) _ p) = _
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext i
  simp

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
