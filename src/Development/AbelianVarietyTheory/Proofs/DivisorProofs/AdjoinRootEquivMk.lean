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

noncomputable section

namespace GlobalTheory.LKCent

section Equiv

variable {F : Type} [Field F] {B : Type} [Ring B] [Algebra F B]

def gen (γ : B) : Algebra.adjoin F ({γ} : Set B) := ⟨γ, Algebra.self_mem_adjoin_singleton F γ⟩

theorem aeval_gen (γ : B) (p : Polynomial F) :
    ((Polynomial.aeval (gen (F := F) γ) p : Algebra.adjoin F ({γ} : Set B)) : B) = Polynomial.aeval γ p :=
  Polynomial.aeval_subalgebra_coe p _ _

def adjoinRootEquiv (γ : B) : AdjoinRoot (minpoly F γ) ≃ₐ[F] Algebra.adjoin F ({γ} : Set B) :=
  AlgEquiv.ofBijective (AdjoinRoot.liftAlgHom (minpoly F γ) (Algebra.ofId F _) (gen γ) (by
      show Polynomial.aeval (gen γ) (minpoly F γ) = 0
      apply Subtype.ext
      rw [aeval_gen, minpoly.aeval]
      rfl)) (by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      induction a using AdjoinRoot.induction_on with
      | ih p =>
        rw [AdjoinRoot.liftAlgHom_mk] at ha
        have h0 : Polynomial.aeval γ p = 0 := by
          have := congrArg Subtype.val ha
          rw [← aeval_gen (F := F) γ p]
          exact this
        exact (AdjoinRoot.mk_eq_zero).2 (minpoly.dvd F γ h0)
    · rintro ⟨y, hy⟩
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨p, rfl⟩ := hy
      refine ⟨AdjoinRoot.mk _ p, ?_⟩
      rw [AdjoinRoot.liftAlgHom_mk]
      apply Subtype.ext
      exact aeval_gen γ p)

end Equiv

section Star

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {B : Type} [Ring B] [StarRing B]
  [Algebra F B] [Algebra k B] [IsScalarTower k F B] (γ : B)

def starL (hk : ∀ t : k, star (algebraMap k B t) = algebraMap k B t)
    (hs : ∀ x ∈ Algebra.adjoin F ({γ} : Set B), star x ∈ Algebra.adjoin F ({γ} : Set B)) :
    Algebra.adjoin F ({γ} : Set B) →ₐ[k] Algebra.adjoin F ({γ} : Set B) where
  toFun x := ⟨star (x : B), hs _ x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by
    have h := mul_comm (⟨star (y : B), hs _ y.2⟩ : Algebra.adjoin F ({γ} : Set B)) ⟨star (x : B), hs _ x.2⟩
    ext
    simpa [star_mul] using congrArg Subtype.val h
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' t := by
    ext
    simp only [Subalgebra.coe_algebraMap]
    exact hk t

@[simp]
theorem coe_starL (hk : ∀ t : k, star (algebraMap k B t) = algebraMap k B t)
    (hs : ∀ x ∈ Algebra.adjoin F ({γ} : Set B), star x ∈ Algebra.adjoin F ({γ} : Set B))
    (x : Algebra.adjoin F ({γ} : Set B)) : ((starL k γ hk hs x : Algebra.adjoin F ({γ} : Set B)) : B) =
      star (x : B) := rfl

end Star

end GlobalTheory.LKCent
