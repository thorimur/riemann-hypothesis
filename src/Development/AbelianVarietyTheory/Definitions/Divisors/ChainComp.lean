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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Presheaf

noncomputable section

namespace GlobalTheory.SSG

def stdStep {C : Type} [CommRing C] (ϖ : C) {n : ℕ} (i : Fin n) : (Fin n → C) →ₗ[C] (Fin n → C) where
  toFun v j := if j = i then ϖ * v j else v j
  map_add' v w := by
    funext j
    by_cases h : j = i <;> simp [h, mul_add]
  map_smul' c v := by
    funext j
    by_cases h : j = i <;> simp [h, smul_eq_mul, mul_left_comm]

structure LMPoint (C : Type) [CommRing C] (ϖ : C) (n : ℕ) [NeZero n] where

  ℓ : Fin n → Submodule C (Fin n → C)

  line : ∀ i, ∃ v : Fin n → C, ℓ i = Submodule.span C {v} ∧ Ideal.span (Set.range v) = ⊤

  step : ∀ i, (ℓ i).map (stdStep ϖ i) ≤ ℓ (i + 1)

def LMPoint.worst {C : Type} [CommRing C] (n : ℕ) [NeZero n] : LMPoint C 0 n where
  ℓ i := Submodule.span C {Pi.single i 1}
  line i := ⟨Pi.single i 1, rfl, by
    rw [eq_top_iff, ← Ideal.span_singleton_one]
    exact Ideal.span_mono (by rintro _ rfl; exact ⟨i, by simp⟩)⟩
  step i := by
    rw [Submodule.map_span, Set.image_singleton]
    have : stdStep (0 : C) i (Pi.single i 1) = 0 := by
      funext j; by_cases h : j = i <;> simp [stdStep, h]
    rw [this, Submodule.span_singleton_eq_bot.2 rfl]
    exact bot_le

def chainComp {C : Type} [CommRing C] {n : ℕ} {M : Fin (n + 1) → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module C (M i)]
    (f : ∀ i : Fin n, M i.castSucc →ₗ[C] M i.succ) : ∀ i : Fin (n + 1), M 0 →ₗ[C] M i :=
  Fin.induction LinearMap.id (fun i g => f i ∘ₗ g)

end GlobalTheory.SSG

end
