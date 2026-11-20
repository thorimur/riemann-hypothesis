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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem repr_algebraMap_of_basis_eq {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (a : F) (k : β) :
    b.repr (algebraMap F A a) k = algebraMap ℚ R (ω.repr a k) := by
  have hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q) :=
    fun q => DFunLike.congr_fun (RingHom.ext_rat ((algebraMap F A).comp (algebraMap ℚ F))
      ((algebraMap R A).comp (algebraMap ℚ R))) q
  have hsum : algebraMap F A a = ∑ i, algebraMap ℚ R (ω.repr a i) • b i := by
    conv_lhs => rw [← ω.sum_repr a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def (ω.repr a i) (ω i), map_mul, hq, hb,
      Algebra.smul_def (algebraMap ℚ R (ω.repr a i))]
  rw [hsum, b.repr_sum_self]

private theorem basis_repr_mul_of_basis_eq_algebraMap {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (u v : A)
    (k : β) : b.repr (u * v) k =
      ∑ i, ∑ j, b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
  have e : ∀ i j, b.repr ((b.repr u i • b i) * (b.repr v j • b j)) k
      = b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
    intro i j
    rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, hb i, hb j, ← map_mul,
      repr_algebraMap_of_basis_eq ω b hb]
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, e]
  exact Finset.sum_comm

theorem exists_coord_polynomial : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (τ : Type) (P : MvPolynomial τ F), ∃ Q : β → MvPolynomial (τ × β) ℚ, ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ (x : τ → A) (k : β), b.repr (MvPolynomial.aeval x P) k = MvPolynomial.aeval (fun p : τ × β => b.repr (x p.1) p.2) (Q k) := by
  intro F β _ _ _ _ ω τ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨fun k => MvPolynomial.C (ω.repr a k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, repr_algebraMap_of_basis_eq ω b hb]
  | add p q hp hq =>
    obtain ⟨Q1, h1⟩ := hp
    obtain ⟨Q2, h2⟩ := hq
    refine ⟨fun k => Q1 k + Q2 k, ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_add, map_add, Finsupp.add_apply, map_add, h1 R A b hb x k, h2 R A b hb x k]
  | mul_X p n hp =>
    obtain ⟨Q1, h1⟩ := hp
    refine ⟨fun k => ∑ i, ∑ j, Q1 i * MvPolynomial.X (n, j) *
      MvPolynomial.C (ω.repr (ω i * ω j) k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_mul, MvPolynomial.aeval_X, basis_repr_mul_of_basis_eq_algebraMap ω b hb]
    simp only [map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, h1 R A b hb x]

end GlobalTheory.ClassFin
