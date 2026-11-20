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
import Mathlib.Topology.Sheaves.Init
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Descent

theorem mem_of_includeRight_mem_map :
  ∀ (O O' R : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O'] [Module.Free O O'] [CommRing R] [Algebra O R] (I : Ideal R) (x : R), (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I → x ∈ I := by
  intro O O' R _ _ _ _ _ _ _ I x hx
  have hnt : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton O' (Module.subsingleton O O')
  have : Module.FaithfullyFlat O O' := inferInstance
  have : Module.FaithfullyFlat R (R ⊗[O] O') := inferInstance
  let c : O' ⊗[O] R ≃ₐ[O] R ⊗[O] O' := Algebra.TensorProduct.comm O O' R
  have hc : ∀ y : R, c (Algebra.TensorProduct.includeRight y) = algebraMap R (R ⊗[O] O') y := by
    intro y
    simp [c, Algebra.TensorProduct.algebraMap_apply]
  have hle : Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I ≤
      Ideal.comap c (Ideal.map (algebraMap R (R ⊗[O] O')) I) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp only [Ideal.mem_comap]
    rw [hc]
    exact Ideal.mem_map_of_mem _ hy
  have h1 : algebraMap R (R ⊗[O] O') x ∈ Ideal.map (algebraMap R (R ⊗[O] O')) I := by
    have h2 := hle hx
    simp only [Ideal.mem_comap] at h2
    rwa [hc] at h2
  have h4 := Ideal.comap_map_eq_self_of_faithfullyFlat (B := R ⊗[O] O') I
  rw [← h4]
  exact h1

end GlobalTheory.CompanionTheory.Descent
