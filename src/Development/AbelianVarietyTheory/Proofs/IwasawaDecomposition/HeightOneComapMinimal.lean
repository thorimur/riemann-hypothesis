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
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
open IsLocalRing

namespace GlobalTheory

theorem comap_eq_of_height_one_of_flat {A B R : Type} [CommRing A] [IsDomain A] [CommRing B]
    [IsNoetherianRing B] [CommRing R] [IsNoetherianRing R] (ι : A →+* B) (ψ : B →+* R)
    (hι : ι.Flat) (hψ : ψ.Flat) (Q : Ideal R) [Q.IsPrime] (hQ : Q.height = 1)
    (hq : Q.comap (ψ.comp ι) ≠ ⊥) (P : Ideal B) (hP : P.IsPrime)
    (hPq : (Q.comap (ψ.comp ι)).map ι ≤ P) (hPQ : P ≤ Q.comap ψ) : P = Q.comap ψ := by
  by_contra hne
  have hlt : P < Q.comap ψ := lt_of_le_of_ne hPQ hne

  obtain ⟨P₁, hP₁Q, hP₁, hP₁P⟩ : ∃ P₁ ≤ Q, P₁.IsPrime ∧ P₁.comap ψ = P := by
    letI := ψ.toAlgebra
    haveI : Module.Flat B R := hψ
    haveI : (Q.comap ψ).IsPrime := Ideal.comap_isPrime ψ Q
    haveI : Q.LiesOver (Q.comap ψ) := ⟨rfl⟩
    obtain ⟨P₁, h1, h2, h3⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P) (q := Q.comap ψ) Q hPQ
    exact ⟨P₁, h1, h2, h3.over.symm⟩
  have hP₁lt : P₁ < Q := by
    refine lt_of_le_of_ne hP₁Q ?_
    rintro rfl
    exact hne hP₁P.symm
  have hP₁h : P₁.height < 1 := by
    have h := (Ideal.height_le_iff (p := Q) (n := 1)).mp (by rw [hQ]; rfl) P₁ hP₁ hP₁lt
    exact_mod_cast h
  have hP₁0 : P₁.height ≤ ((0 : ℕ) : ℕ∞) := by
    have : P₁.height < ((1 : ℕ) : ℕ∞) := by exact_mod_cast hP₁h
    exact Order.le_of_lt_succ (by simpa using this)

  have hmin : ∀ P₂ : Ideal R, P₂.IsPrime → ¬ P₂ < P₁ := by
    intro P₂ hP₂ h
    haveI := hP₁
    have := (Ideal.height_le_iff (p := P₁) (n := 0)).mp hP₁0 P₂ hP₂ h
    exact absurd this (by simp)

  have hbot : P.comap ι = ⊥ := by
    by_contra hp
    letI := (ψ.comp ι).toAlgebra
    haveI : Module.Flat A R := hι.comp hψ
    haveI : P₁.IsPrime := hP₁
    haveI : (P.comap ι).IsPrime := Ideal.comap_isPrime ι P
    haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    haveI : P₁.LiesOver (P.comap ι) := ⟨by rw [← hP₁P]; rfl⟩
    obtain ⟨P₂, h1, h2, h3⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal A)) (q := P.comap ι) P₁ bot_le
    refine hmin P₂ h2 (lt_of_le_of_ne h1 ?_)
    rintro rfl
    apply hp
    rw [← hP₁P]
    exact h3.over.symm
  apply hq
  refine le_bot_iff.mp ?_
  rw [← hbot]
  exact (Ideal.le_comap_map).trans (Ideal.comap_mono hPq)

end GlobalTheory
