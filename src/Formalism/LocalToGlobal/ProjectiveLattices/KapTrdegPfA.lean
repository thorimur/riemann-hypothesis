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
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Presheaf

namespace Formalism.L2.Pj.TranscendenceDegreeLemmas

open Algebra

theorem trdeg_residueField_of_minimal {K A : Type} [Field K] [CommRing A] [Algebra K A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A) :
    Algebra.trdeg K p.ResidueField = n := by
  classical
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K A
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin n) K) A :=
    IsScalarTower.of_algebraMap_eq' (g.comp_algebraMap).symm
  have : Algebra.Etale (MvPolynomial (Fin n) K) A := hg
  have hq : p.under (MvPolynomial (Fin n) K) = ⊥ := by
    by_contra hne
    have : p.LiesOver (p.under (MvPolynomial (Fin n) K)) := ⟨rfl⟩
    obtain ⟨P, hPlt, hP, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥)
      (q := p.under (MvPolynomial (Fin n) K)) p (bot_lt_iff_ne_bot.mpr hne)
    exact (not_le_of_gt hPlt) (hp.2 ⟨hP, bot_le⟩ hPlt.le)
  have : p.LiesOver (⊥ : Ideal (MvPolynomial (Fin n) K)) := ⟨hq.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal (MvPolynomial (Fin n) K)) p
  have : Localization.AtPrime.IsLiesOverAlgebra (⊥ : Ideal (MvPolynomial (Fin n) K)) p := ⟨rfl⟩
  have : Algebra.FormallyUnramified A (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.of_isLocalization p.primeCompl
  have : Algebra.IsUnramifiedAt (MvPolynomial (Fin n) K) p :=
    Algebra.FormallyUnramified.comp (MvPolynomial (Fin n) K) A (Localization.AtPrime p)
  have : Module.Finite (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField := inferInstance
  have : Algebra.IsAlgebraic (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField :=
    inferInstance
  have : Algebra.IsAlgebraic (MvPolynomial (Fin n) K) (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have : FaithfulSMul (MvPolynomial (Fin n) K) (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  have : IsScalarTower K (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField := inferInstance
  have h1 := trdeg_add_eq K (MvPolynomial (Fin n) K) (A := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField)
  have h2 := trdeg_add_eq K (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField (A := p.ResidueField)
  rw [trdeg_eq_zero (R := MvPolynomial (Fin n) K) (A := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField), add_zero] at h1
  rw [trdeg_eq_zero (R := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField) (A := p.ResidueField), add_zero] at h2
  rw [← h2, ← h1, MvPolynomial.trdeg_of_isDomain]
  simp

end Formalism.L2.Pj.TranscendenceDegreeLemmas
