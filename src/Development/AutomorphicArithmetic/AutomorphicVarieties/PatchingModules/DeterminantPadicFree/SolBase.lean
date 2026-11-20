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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.solBase :
    ∀ {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ} (e : ι → F) (r : ι → Matrix (Fin n) (Fin n) F), (∀ X : Matrix (Fin n) (Fin n) F, (∀ i, e i • (r i * X) = X * r i) → X = 0) → ∀ X : Matrix (Fin n) (Fin n) F', (∀ i, f (e i) • ((r i).map f * X) = X * (r i).map f) → X = 0 := by
  intro F F' ι _ _ f n e r h X hX
  letI : Algebra F F' := f.toAlgebra
  have hs : ∀ (x : F) (y : F'), f x * y = x • y := fun x y => (Algebra.smul_def x y).symm
  let b := Module.Basis.ofVectorSpace F F'
  have key : ∀ k, (Matrix.of fun a c => b.repr (X a c) k) = 0 := by
    intro k
    apply h
    intro i
    ext a c
    have hac := congrArg (fun M => b.repr (M a c) k) (hX i)
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Matrix.of_apply] at hac ⊢
    simp only [hs, mul_comm (X _ _) (f _), ← Finset.smul_sum, map_sum, map_smul, Finsupp.smul_apply,
      Finsupp.coe_finset_sum, Finset.sum_apply, smul_eq_mul] at hac
    rw [hac]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  ext a c
  have hk : b.repr (X a c) = 0 := by
    ext k
    exact congrFun (congrFun (key k) a) c
  simpa using hk
