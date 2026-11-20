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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem tensor_projective_dvd_of_coord_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  intro O M _ _ _ N _ _ _ _ a z h
  obtain ⟨s, hs⟩ := (Module.Projective.out : ∃ s : M →ₗ[O] M →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  obtain ⟨s', hs'⟩ := (Module.Projective.out : ∃ s : N →ₗ[O] N →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  have hf : ∀ (w : M ⊗[O] N) (p : M × N), finsuppTensorFinsupp' O M N (TensorProduct.map s s' w) p =
      TensorProduct.dualDistrib O M N ((Finsupp.lapply p.1 ∘ₗ s) ⊗ₜ (Finsupp.lapply p.2 ∘ₗ s')) w := by
    intro w ⟨i, j⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [finsuppTensorFinsupp'_apply_apply, dualDistrib_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  set f := finsuppTensorFinsupp' O M N (TensorProduct.map s s' z) with hfdef
  have hdiv : ∀ p, a ∣ f p := fun p => by rw [hfdef, hf]; exact h _ _
  choose c hc using hdiv
  let g : M × N →₀ O := ∑ p ∈ f.support, Finsupp.single p (c p)
  have hg : f = a • g := by
    simp only [g, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, ← hc]
    exact (Finsupp.sum_single f).symm
  have hid : (Finsupp.linearCombination O id : (M →₀ O) →ₗ[O] M) ∘ₗ s = LinearMap.id :=
    LinearMap.ext hs
  have hid' : (Finsupp.linearCombination O id : (N →₀ O) →ₗ[O] N) ∘ₗ s' = LinearMap.id :=
    LinearMap.ext hs'
  refine ⟨TensorProduct.map (Finsupp.linearCombination O id) (Finsupp.linearCombination O id)
    ((finsuppTensorFinsupp' O M N).symm g), ?_⟩
  rw [← map_smul, ← map_smul, ← hg, hfdef, LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, hid, hid', TensorProduct.map_id, LinearMap.id_apply]

end GlobalTheory
