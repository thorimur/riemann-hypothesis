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
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

open MvPolynomial in
theorem optionEquivLeft_pderiv_none (A : Type) [CommRing A] (n : ℕ)
    (p : MvPolynomial (Option (Fin n)) A) :
    optionEquivLeft A (Fin n) (pderiv none p) = Polynomial.derivative (optionEquivLeft A (Fin n) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [optionEquivLeft_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rcases i with _ | j
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_none, mul_comm]
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_some, pderiv_X, mul_comm]

open MvPolynomial in
theorem eval_map_eq_eval₂_optionEquivLeft (A : Type) [CommRing A] (n : ℕ) {k : Type} [Field k]
    (ψ : A →+* k) (Q : Option (Fin n) → k) (p : MvPolynomial (Option (Fin n)) A) :
    eval Q (map ψ p) = Polynomial.eval₂ (eval₂Hom ψ (Q ∘ some)) (Q none) (optionEquivLeft A (Fin n) p) := by
  rw [MvPolynomial.eval_map]
  change eval₂Hom ψ Q p = (Polynomial.eval₂RingHom (eval₂Hom ψ (Q ∘ some)) (Q none)).comp
    (optionEquivLeft A (Fin n)).toAlgHom.toRingHom p
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [optionEquivLeft_C]
  · rcases i with _ | j <;> simp [optionEquivLeft_X_none, optionEquivLeft_X_some]

open MvPolynomial in
theorem optionEquivLeft_map (A : Type) [CommRing A] (n : ℕ) {k : Type} [Field k]
    (ψ : A →+* k) (p : MvPolynomial (Option (Fin n)) A) :
    optionEquivLeft k (Fin n) (map ψ p) = Polynomial.map (map ψ) (optionEquivLeft A (Fin n) p) := by
  change (optionEquivLeft k (Fin n)).toAlgHom.toRingHom.comp (map ψ) p =
    (Polynomial.mapRingHom (map ψ)).comp (optionEquivLeft A (Fin n)).toAlgHom.toRingHom p
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [optionEquivLeft_C]
  · rcases i with _ | j <;> simp [optionEquivLeft_X_none, optionEquivLeft_X_some]

open MvPolynomial in

theorem standardEtale_mvPolynomial_hypersurface :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
      [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B],
      Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B →
      ∃ (f g : MvPolynomial (Option (Fin n)) A), (∀ (k : Type) [Field k] (ψ : A →+* k),
        MvPolynomial.map ψ f ≠ 0) ∧
      (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : Option (Fin n) → k),
        MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 →
        MvPolynomial.eval Q (MvPolynomial.pderiv none (MvPolynomial.map ψ f)) ≠ 0) ∧
      Nonempty (B ≃ₐ[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)) := by
  intro A B _ _ _ n _ _ hB
  obtain ⟨P⟩ := hB.nonempty_standardEtalePresentation
  set e := optionEquivLeft A (Fin n) with he
  refine ⟨e.symm P.f, e.symm P.g, ?_, ?_, ?_⟩
  · intro k _ ψ h
    have h1 := optionEquivLeft_map A n ψ (e.symm P.f)
    rw [h, map_zero, ← he, e.apply_symm_apply] at h1
    exact (P.monic_f.map (MvPolynomial.map ψ)).ne_zero h1.symm
  · intro k _ ψ Q hf hg
    obtain ⟨p₁, p₂, m, hc⟩ := P.cond
    set Φ := Polynomial.eval₂RingHom (eval₂Hom ψ (Q ∘ some)) (Q none)
    have key : ∀ p, eval Q (map ψ p) = Φ (e p) := fun p => eval_map_eq_eval₂_optionEquivLeft A n ψ Q p
    rw [key, e.apply_symm_apply] at hf hg
    rw [pderiv_map, key, optionEquivLeft_pderiv_none, ← he, e.apply_symm_apply]
    intro hd
    have := congrArg Φ hc
    simp only [map_add, map_mul, map_pow] at this
    change Φ (Polynomial.derivative P.f) * _ + _ = _ at this
    rw [hd, hf] at this
    simp only [zero_mul, add_zero] at this
    exact (pow_ne_zero m hg) this.symm
  · let qe : (MvPolynomial (Option (Fin n)) A ⧸ Ideal.span {e.symm P.f}) ≃ₐ[A] AdjoinRoot P.f :=
      Ideal.quotientEquivAlg _ _ e (by rw [Ideal.map_span, Set.image_singleton]; simp)
    have hM : Submonoid.map qe (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {e.symm P.f}) (e.symm P.g))) =
        Submonoid.powers (AdjoinRoot.mk P.f P.g) := by
      rw [Submonoid.map_powers]
      congr 1
      refine (Ideal.quotientEquivAlg_mk (f := e) (x := e.symm P.g) ..).trans ?_
      rw [AlgEquiv.apply_symm_apply]
      rfl
    let le := IsLocalization.algEquivOfAlgEquiv (Localization.Away (Ideal.Quotient.mk (Ideal.span {e.symm P.f}) (e.symm P.g)))
      (Localization.Away (AdjoinRoot.mk P.f P.g)) qe hM
    exact ⟨((P.equivRing.trans P.P.equivAwayAdjoinRoot).restrictScalars A).trans le.symm⟩

end GlobalTheory
