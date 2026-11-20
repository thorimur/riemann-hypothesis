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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
open Finset

namespace GlobalTheory

theorem sum_update_fiber_count {ι : Type} [Fintype ι] [DecidableEq ι] {m : ι → ℕ} (i₀ : ι)
    (G : (∀ i, Fin (m i)) → ℂ) :
    ∑ J : (∀ i, Fin (m i)), ∑ j : Fin (m i₀), G (Function.update J i₀ j) = (m i₀ : ℂ) * ∑ J, G J := by
  let e : (∀ i, Fin (m i)) × Fin (m i₀) ≃ (∀ i, Fin (m i)) × Fin (m i₀) :=
    { toFun := fun p => (Function.update p.1 i₀ p.2, p.1 i₀)
      invFun := fun p => (Function.update p.1 i₀ p.2, p.1 i₀)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  rw [← Fintype.sum_prod_type' (fun J j => G (Function.update J i₀ j))]
  rw [Fintype.sum_equiv e (fun p => G (Function.update p.1 i₀ p.2)) (fun p => G p.1) (fun p => rfl)]
  rw [Fintype.sum_prod_type' (fun J (_ : Fin (m i₀)) => G J)]
  simp [Finset.mul_sum]

theorem sum_prod_update_regroup : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by
  intro ι _ _ X W _ _ m k ℓ i₀ F F' w w' hone v
  have key : ∀ (u : W i₀) (H : (∀ i, X i) → ℂ) (J : ∀ i, Fin (m i)),
      ∑ j, (∏ i, ℓ i (Function.update J i₀ j i) (Function.update v i₀ u i)) *
          H (fun i => k i (Function.update J i₀ j i))
        = (∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (J i) (v i)) *
          ∑ j, ℓ i₀ j u * H (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) := by
    intro u H J
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.prod_eq_mul_prod_compl i₀]
    have hrest : ∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (Function.update J i₀ j i) (Function.update v i₀ u i)
        = ∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (J i) (v i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ i₀ := by simpa using hi
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    have hk : (fun i => k i (Function.update J i₀ j i)) = Function.update (fun i => k i (J i)) i₀ (k i₀ j) := by
      funext i
      exact Function.apply_update k J i₀ j i
    rw [hrest, hk, Function.update_self, Function.update_self]
    ring
  by_cases hm : m i₀ = 0
  · haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by
      have h := J i₀
      rw [hm] at h
      exact h.elim0⟩
    simp
  · have hm' : (m i₀ : ℂ) ≠ 0 := by exact_mod_cast hm
    apply mul_left_cancel₀ hm'
    rw [← sum_update_fiber_count, ← sum_update_fiber_count]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [key w' F J, key w F' J, hone J]

end GlobalTheory
