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

theorem UpperTheory.Reformulated.B.Qp1.exists_limit_of_approx.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R)
    [IsPrecomplete I R] (P : ℕ → R → Prop),
    (∀ (n : ℕ) (x : R), P n x → ∃ (y : R), y - x ∈ I ^ n ∧ P (n + (1 : ℕ)) y) →
      ∀ {x₀ : R}, P (0 : ℕ) x₀ → ∃ (x : R), ∀ (n : ℕ), ∃ (y : R), P n y ∧ x - y ∈ I ^ n := by
  intro R _ I hI P h x₀ h₀
  choose g hg hP using h
  let f : (n : ℕ) → {x : R // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : R // P n x}) ⟨x₀, h₀⟩
      (fun n x => ⟨g n x.1 x.2, hP n x.1 x.2⟩) n
  have hstep : ∀ n, (f (n + 1)).1 - (f n).1 ∈ I ^ n := fun n => hg n (f n).1 (f n).2
  have hdiff : ∀ m n, m ≤ n → (f n).1 - (f m).1 ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : (f (n + 1)).1 - (f n).1 ∈ I ^ m := Ideal.pow_le_pow_right hmn (hstep n)
      have h2 := (I ^ m).add_mem h1 ih
      rwa [sub_add_sub_cancel] at h2
  have htop : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hI (f := fun n => (f n).1) (by
    intro m n hmn
    refine SModEq.symm ?_
    rw [SModEq.sub_mem, htop]
    exact hdiff m n hmn)
  refine ⟨L, fun n => ⟨(f n).1, (f n).2, ?_⟩⟩
  have h3 := (hL n).symm
  rwa [SModEq.sub_mem, htop] at h3
