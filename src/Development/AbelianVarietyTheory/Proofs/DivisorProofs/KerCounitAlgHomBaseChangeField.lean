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
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
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

open TensorProduct

namespace GlobalTheory

theorem ker_counitAlgHom_baseChange_field (O B κ : Type) [CommRing O] [CommRing B] [Bialgebra O B]
    [Field κ] [Algebra O κ] :
    RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B)) =
      Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B)
        (RingHom.ker (Bialgebra.counitAlgHom O B)) := by
  have hs : Function.Surjective (Bialgebra.counitAlgHom O B) := fun c =>
    ⟨algebraMap O B c, by simp⟩
  rw [← Algebra.TensorProduct.lTensor_ker _ hs]
  have key : ∀ x : κ ⊗[O] B, Bialgebra.counitAlgHom κ (κ ⊗[O] B) x =
      Algebra.TensorProduct.rid O κ κ
        (Algebra.TensorProduct.map (AlgHom.id O κ) (Bialgebra.counitAlgHom O B) x) := by
    intro x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c b => simp [TensorProduct.counit_tmul]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, key, map_eq_zero_iff _ (AlgEquiv.injective _)]

theorem hopf_order_formula_fibre :
    (∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Module.finrank k A = Module.finrank k (A ⧸ Ideal.map (f : B →ₐ[k] A) (RingHom.ker (Bialgebra.counitAlgHom k B))) * Module.finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap)) → ∀ (O A B κ : Type) [CommRing O] [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B] [Module.Finite O A] [Field κ] [Algebra O κ] (f : B →ₐc[O] A), Module.finrank κ (TensorProduct O κ A) = Module.finrank κ (TensorProduct O κ (A ⧸ Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B)))) * Module.finrank κ (LinearMap.range ((f : B →ₐ[O] A).toLinearMap.baseChange κ)) := by
  intro H O A B κ _ _ _ _ _ _ _ _ f
  have h := H κ (κ ⊗[O] A) (κ ⊗[O] B) (Bialgebra.TensorProduct.map (BialgHom.id κ κ) f)
  have hI : Ideal.map ((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A)
        (RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B))) =
      Ideal.map (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A)
        (Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B))) := by
    rw [ker_counitAlgHom_baseChange_field]
    refine (Ideal.map_map
      ((Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B) : B →+* κ ⊗[O] B)
      ((((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A)) : κ ⊗[O] B →+* κ ⊗[O] A)).trans ?_
    refine Eq.trans ?_ (Ideal.map_map ((f : B →ₐ[O] A) : B →+* A)
      ((Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A) : A →+* κ ⊗[O] A)).symm
    congr 1
  have hL : ((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A).toLinearMap =
      (f : B →ₐ[O] A).toLinearMap.baseChange κ := by
    ext b
    simp
  rw [hI, hL] at h
  rw [h, (Algebra.TensorProduct.tensorQuotientEquiv (R := O) κ A κ
    (Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B)))).toLinearEquiv.finrank_eq]

end GlobalTheory
