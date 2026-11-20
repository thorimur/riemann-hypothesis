import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem exists_basicOpen_free_avoiding_finite : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (n : ℕ) (V : X.Opens), IsAffineOpen V → IsAffineOpen (f ⁻¹ᵁ V) → (letI := (f.app V).hom.toAlgebra; Module.Free Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.finrank Γ(X, V) Γ(Y, f ⁻¹ᵁ V) = n) → ∀ (x : X), x ∈ V → ∀ (T : Set X), T.Finite → (∀ y ∈ T, IsClosed ({y} : Set X)) → x ∉ T → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧ (∀ y ∈ T, y ∉ W) ∧ IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W) ∧ (letI := (f.app W).hom.toAlgebra; Module.Free Γ(X, W) Γ(Y, f ⁻¹ᵁ W) ∧ Module.Finite Γ(X, W) Γ(Y, f ⁻¹ᵁ W) ∧ Module.finrank Γ(X, W) Γ(Y, f ⁻¹ᵁ W) = n) := by
  intro X Y f n V hV hV' hfree x hx T hT hcl hxT
  have hTc : IsClosed T := by
    rw [← Set.biUnion_of_singleton T]
    exact hT.isClosed_biUnion hcl
  let O : X.Opens := V ⊓ ⟨Tᶜ, hTc.isOpen_compl⟩
  obtain ⟨a, haO, hxa⟩ := hV.exists_basicOpen_le (V := O) ⟨x, hx, hxT⟩ hx
  refine ⟨X.basicOpen a, hxa, X.basicOpen_le a, fun y hy hya => (haO hya).2 hy, hV.basicOpen a,
    ?_, ?_⟩
  · rw [Scheme.preimage_basicOpen]; exact hV'.basicOpen _
  letI : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  obtain ⟨hF, hFin, hr⟩ := hfree
  letI : Algebra Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    (f.app (X.basicOpen a)).hom.toAlgebra
  let iX : X.basicOpen a ⟶ V := homOfLE (X.basicOpen_le a)
  let iY : f ⁻¹ᵁ X.basicOpen a ⟶ f ⁻¹ᵁ V := homOfLE (fun y hy => X.basicOpen_le a hy)
  letI : Algebra Γ(X, V) Γ(X, X.basicOpen a) := (X.presheaf.map iX.op).hom.toAlgebra
  letI : Algebra Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a) := (Y.presheaf.map iY.op).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    ((algebraMap Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).comp
      (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V))).toAlgebra
  haveI : IsScalarTower Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hcomm : (algebraMap Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).comp
      (algebraMap Γ(X, V) Γ(X, X.basicOpen a)) =
      (algebraMap Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).comp
        (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V)) :=
    congrArg CommRingCat.Hom.hom (f.naturality iX.op)
  haveI : IsScalarTower Γ(X, V) Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    IsScalarTower.of_algebraMap_eq' hcomm.symm
  haveI : IsLocalization.Away a Γ(X, X.basicOpen a) := hV.isLocalization_basicOpen a
  haveI : IsLocalization.Away (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V) a)
      Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    hV'.isLocalization_of_eq_basicOpen _ iY (Scheme.preimage_basicOpen f a)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ V) (Submonoid.powers a))
      Γ(Y, f ⁻¹ᵁ X.basicOpen a) := by
    rw [Algebra.algebraMapSubmonoid_powers]; infer_instance
  haveI : IsLocalizedModule (Submonoid.powers a)
      (IsScalarTower.toAlgHom Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr this
  have hbc : IsBaseChange Γ(X, X.basicOpen a)
      (IsScalarTower.toAlgHom Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) Γ(X, X.basicOpen a) _).mp
      inferInstance
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  haveI : Nonempty (X.basicOpen a) := ⟨⟨x, hxa⟩⟩
  haveI : Nontrivial Γ(X, V) := Scheme.component_nontrivial X V
  haveI : Nontrivial Γ(X, X.basicOpen a) := Scheme.component_nontrivial X _
  let b := Module.Free.chooseBasis Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
  let b' := hbc.basis b
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  rw [Module.finrank_eq_card_basis b', ← hr, Module.finrank_eq_card_basis b]

end GlobalTheory
