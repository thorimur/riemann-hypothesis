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

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkDedekind :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (K : Type) [Field K] [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (f : Perm (Fin n) → K),
      (∀ x : MvPolynomial (Fin n) R, ∑ u, f u * algebraMap _ K (rename u x) = 0) → f = 0 := by
  intro R _ _ n K _ _ _ f hf
  classical
  let φ : Perm (Fin n) → (MvPolynomial (Fin n) R →* K) := fun u =>
    (algebraMap (MvPolynomial (Fin n) R) K).toMonoidHom.comp (rename u : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).toRingHom.toMonoidHom
  have hinj : Function.Injective φ := by
    intro u v huv
    ext i
    have h := DFunLike.congr_fun huv (X i)
    simp only [φ, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_toRingHom, rename_X] at h
    have h2 := IsFractionRing.injective (MvPolynomial (Fin n) R) K h
    exact congrArg Fin.val (X_injective h2)
  have hli := (linearIndependent_monoidHom (MvPolynomial (Fin n) R) K).comp φ hinj
  rw [Fintype.linearIndependent_iff] at hli
  funext u
  apply hli f
  funext x
  simpa [φ, Finset.sum_apply] using hf x
