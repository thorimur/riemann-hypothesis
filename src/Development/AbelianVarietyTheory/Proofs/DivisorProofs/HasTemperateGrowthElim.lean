import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

namespace GlobalTheory.SliceSchwartz

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def inrL (κ κ' : Type) [Fintype κ] [Fintype κ'] : (κ' → V) →L[ℝ] (κ ⊕ κ' → V) :=
  ContinuousLinearMap.pi fun i =>
    Sum.elim (fun _ : κ => (0 : (κ' → V) →L[ℝ] V)) (fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ' => V) j) i

theorem elim_eq_add {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    (fun y : κ' → V => (Sum.elim x y : κ ⊕ κ' → V)) = fun y => Sum.elim x 0 + inrL κ κ' y := by
  funext y i
  cases i with
  | inl i => simp [inrL]
  | inr j => simp [inrL]

theorem hasTemperateGrowth_elim {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    Function.HasTemperateGrowth (fun y : κ' → V => (Sum.elim x y : κ ⊕ κ' → V)) := by
  rw [elim_eq_add]
  exact (Function.HasTemperateGrowth.const _).add (ContinuousLinearMap.hasTemperateGrowth (inrL (V := V) κ κ'))

theorem norm_le_norm_elim {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (y : κ' → V) :
    ‖y‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm (Sum.elim x y : κ ⊕ κ' → V) (Sum.inr j)

theorem elim_upper {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    ∃ (k : ℕ) (C : ℝ), ∀ y : κ' → V, ‖y‖ ≤ C * (1 + ‖(Sum.elim x y : κ ⊕ κ' → V)‖) ^ k :=
  ⟨1, 1, fun y => by rw [pow_one, one_mul]; linarith [norm_le_norm_elim x y]⟩

def sliceR {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) :
    SchwartzMap (κ' → V) ℂ :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_elim x) (elim_upper x) f

@[simp] theorem sliceR_apply {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V)
    (y : κ' → V) : sliceR f x y = f (Sum.elim x y) := rfl

def sliceRL {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ' → V) ℂ :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_elim x) (elim_upper x)

theorem sliceRL_apply {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    sliceRL x f = sliceR f x := rfl

end GlobalTheory.SliceSchwartz
