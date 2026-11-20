import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory

theorem surjective_of_epi_of_field_to_field {K L : Type} [Field K] [Field L]
    (φ : CommRingCat.of K ⟶ CommRingCat.of L) [Epi φ] : Function.Surjective φ.hom := by
  letI : Algebra K L := φ.hom.toAlgebra
  have h : ∀ a : L, (a ⊗ₜ[K] (1 : L)) = (1 : L) ⊗ₜ[K] a := by
    intro a
    have e : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L))
        = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom := by
      rw [← cancel_epi φ]
      ext c
      exact congr($(Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := K) (A := L) (B := L)) c)
    exact congr(($e).hom a)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  have g1 : g 1 = 1 := by simpa using congr($hg 1)
  intro a
  refine ⟨g a, ?_⟩
  have := congr(TensorProduct.rid K L (LinearMap.lTensor L g $(h a)))
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at this
  exact (Algebra.algebraMap_eq_smul_one (A := L) (g a)).trans this.symm

theorem residueFieldMap_surjective_of_mono {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X) :
    Function.Surjective (f.residueFieldMap x).hom := by
  have h1 : Mono (Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x)) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  have h2 : Mono (Spec.map (f.residueFieldMap x)) := mono_of_mono _ (Y.fromSpecResidueField (f x))
  have h3 : Mono (f.residueFieldMap x).op :=
    Scheme.Spec.mono_of_mono_map (f := (f.residueFieldMap x).op) h2
  have h4 : Epi (f.residueFieldMap x) := (CategoryTheory.op_mono_iff _).1 h3
  exact surjective_of_epi_of_field_to_field (K := Y.residueField (f x)) (L := X.residueField x) (f.residueFieldMap x)

end GlobalTheory
