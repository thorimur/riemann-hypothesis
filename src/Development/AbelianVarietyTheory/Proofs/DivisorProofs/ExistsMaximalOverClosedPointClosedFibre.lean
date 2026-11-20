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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init
open IsLocalRing Polynomial

namespace GlobalTheory

theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  intro T E _ _ _ _ _ Q hQp hQ
  set P : Ideal T[X] := (maximalIdeal T).map (C : T →+* T[X]) with hPdef
  set f := algebraMap T[X] E with hfdef
  obtain ⟨y, hy, hQy⟩ := Ideal.exists_le_maximal Q hQp.ne_top
  have hPy : P ≤ y.comap f := hQ ▸ Ideal.comap_mono hQy

  letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _
  have eP := Ideal.polynomialQuotientEquivQuotientPolynomial (maximalIdeal T)
  haveI : IsJacobsonRing (T[X] ⧸ P) := isJacobsonRing_of_surjective ⟨eP.toRingHom, eP.surjective⟩
  have hPnf : ¬ P.IsMaximal := by
    intro hm
    have hf : IsField (T[X] ⧸ P) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).1 hm
    exact Polynomial.not_isField (T ⧸ maximalIdeal T) (MulEquiv.isField hf eP.toMulEquiv)

  let φ : T[X] ⧸ P →+* E ⧸ y := Ideal.quotientMap y f hPy
  have hcomp : φ.comp (Ideal.Quotient.mk P) = (Ideal.Quotient.mk y).comp f := Ideal.quotientMap_comp_mk hPy
  have hft : φ.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk P)
    rw [hcomp]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective)
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Field (E ⧸ y) := Ideal.Quotient.field y
  letI : Algebra (T[X] ⧸ P) (E ⧸ y) := φ.toAlgebra
  haveI : Algebra.FiniteType (T[X] ⧸ P) (E ⧸ y) := hft
  haveI : Module.Finite (T[X] ⧸ P) (E ⧸ y) := finite_of_finite_type_of_isJacobsonRing _ _
  have hker : (RingHom.ker φ).IsMaximal := by
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := T[X] ⧸ P) (⊥ : Ideal (E ⧸ y))
    rwa [← RingHom.ker_eq_comap_bot] at this
  have hyc : y.comap f = (RingHom.ker φ).comap (Ideal.Quotient.mk P) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  have hymax : (y.comap f).IsMaximal := by
    rw [hyc]; exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨y, hy, hQy, fun h => hPnf (h ▸ hymax), ?_⟩
  have hle : maximalIdeal T ≤ (y.comap f).comap C := by
    intro a ha
    exact hPy (Ideal.mem_map_of_mem _ ha)
  have hne : (y.comap f).comap (C : T →+* T[X]) ≠ ⊤ := (Ideal.comap_isPrime C (y.comap f)).ne_top
  exact ((maximalIdeal.isMaximal T).eq_of_le hne hle).symm

end GlobalTheory
