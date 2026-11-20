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

namespace GlobalTheory

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem formallyEtale_mvPolynomial_eval₂_tensor {k R B : Type} [CommRing k] [CommRing R]
    [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B)
    (hf : (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale) :
    (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by
  set f := MvPolynomial.eval₂Hom (algebraMap k B) τ with hfdef
  set g := MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i) with hgdef
  letI : Algebra (MvPolynomial (Fin r) k) B := f.toAlgebra
  letI : Algebra (MvPolynomial (Fin r) R) (R ⊗[k] B) := g.toAlgebra
  letI : Algebra B (R ⊗[k] B) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra (MvPolynomial (Fin r) k) (R ⊗[k] B) :=
    (g.comp (algebraMap (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R))).toAlgebra
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) k) B := hf
  have key : g.comp (algebraMap (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R)) =
      (algebraMap B (R ⊗[k] B)).comp f := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C, f, g,
        MvPolynomial.eval₂Hom_C]
      show (algebraMap k R a) ⊗ₜ[k] (1 : B) = (1 : R) ⊗ₜ[k] algebraMap k B a
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_X, f, g,
        MvPolynomial.eval₂Hom_X']
      rfl
  haveI : IsScalarTower k (MvPolynomial (Fin r) k) B := IsScalarTower.of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, f, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_def]
  haveI : IsScalarTower k B (R ⊗[k] B) := IsScalarTower.of_algebraMap_eq fun x =>
    ((Algebra.TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B).commutes x).symm
  haveI : IsScalarTower (MvPolynomial (Fin r) k) B (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, key]; rfl
  haveI : IsScalarTower (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower k (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra, g, MvPolynomial.algebraMap_eq,
        Algebra.TensorProduct.algebraMap_apply]
  haveI : IsScalarTower R (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra, g, MvPolynomial.algebraMap_eq,
        Algebra.TensorProduct.algebraMap_apply]
  haveI h1 : Algebra.IsPushout k B R (R ⊗[k] B) := inferInstance
  haveI h2 : Algebra.IsPushout (MvPolynomial (Fin r) k) B (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    (Algebra.IsPushout.comp_iff k (MvPolynomial (Fin r) k) R (MvPolynomial (Fin r) R)
      (T := B) (T' := R ⊗[k] B)).1 h1
  haveI : Algebra.IsPushout (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) B (R ⊗[k] B) :=
    h2.symm
  have : Algebra.FormallyEtale (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    Algebra.FormallyEtale.of_equiv
      (Algebra.IsPushout.equiv (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) B (R ⊗[k] B))
  exact this

end GlobalTheory
