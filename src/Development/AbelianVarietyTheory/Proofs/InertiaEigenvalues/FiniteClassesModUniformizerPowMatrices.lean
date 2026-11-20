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
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.GenUnr

theorem finite_classes_mod_pow (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
    (r t : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (N : ℕ) :
    ∃ T : Finset (Matrix (Fin r ⊕ Fin t) (Fin r) K),
      ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O),
        algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K) →
        ∃ y ∈ T, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O,
          x = y + (ϖ ^ N • z').map (algebraMap O K) := by
  classical
  have hfin : Finite (O ⧸ Ideal.span {ϖ ^ (2 * N)}) :=
    IsLocalRing.finite_quotient_iff.mpr
      ⟨2 * N, by rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩
  haveI := Fintype.ofFinite (Matrix (Fin r ⊕ Fin t) (Fin r) (O ⧸ Ideal.span {ϖ ^ (2 * N)}))
  have hϖK : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hϖ.ne_zero
  let lift : O ⧸ Ideal.span {ϖ ^ (2 * N)} → O := fun c => (Ideal.Quotient.mk_surjective c).choose
  have hlift : ∀ c, Ideal.Quotient.mk _ (lift c) = c := fun c =>
    (Ideal.Quotient.mk_surjective c).choose_spec
  let rep : Matrix (Fin r ⊕ Fin t) (Fin r) (O ⧸ Ideal.span {ϖ ^ (2 * N)}) →
      Matrix (Fin r ⊕ Fin t) (Fin r) K :=
    fun c => (algebraMap O K (ϖ ^ N))⁻¹ • (c.map lift).map (algebraMap O K)
  refine ⟨Finset.univ.image rep, fun x z hxz => ?_⟩
  have hdiff : ∀ i j, ∃ a : O, a * ϖ ^ (2 * N) = z i j - lift (Ideal.Quotient.mk _ (z i j)) :=
    fun i j => Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp (hlift _).symm)
  choose w hw using hdiff
  refine ⟨rep (z.map (Ideal.Quotient.mk _)), Finset.mem_image_of_mem _ (Finset.mem_univ _), Matrix.of w, ?_⟩
  ext i j
  have hx := congrFun (congrFun hxz i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, map_pow] at hx
  have hz : lift (Ideal.Quotient.mk _ (z i j)) = z i j - w i j * ϖ ^ (2 * N) := by
    rw [hw]; ring
  simp only [rep, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hz, map_sub,
    map_mul, map_pow, Matrix.of_apply, ← hx]
  field_simp
  ring

end GlobalTheory.GenUnr
