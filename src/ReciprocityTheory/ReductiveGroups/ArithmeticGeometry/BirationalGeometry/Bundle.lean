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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

section Chart

variable (o : Type*) {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι : Type*}

def chartRing (x : ι → Ω) (i : ι) : Subalgebra o Ω :=
  Algebra.adjoin o (Set.range fun j => x j / x i)

structure ChartBundle (x : ι → Ω) (r : ℕ) (E : Type*) [AddCommGroup E] [Module Ω E] where

  lat : ι → AddSubgroup E

  stable : ∀ i, ∀ a ∈ chartRing o x i, ∀ e ∈ lat i, a • e ∈ lat i

  frame : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing o x i) ∧
    (∀ l, c l ∈ chartRing o x i) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ lat i) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing o x i) ∧ e = ∑ q, a q • b q

  overlap : ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ lat i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ lat j

variable {o}

def globalSec {x : ι → Ω} {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (B : ChartBundle o x r E) : AddSubgroup E :=
  ⨅ (i) (_ : x i ≠ 0), B.lat i

theorem mem_globalSec {x : ι → Ω} {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (B : ChartBundle o x r E) (e : E) :
    e ∈ globalSec B ↔ ∀ i, x i ≠ 0 → e ∈ B.lat i := by
  simp [globalSec, AddSubgroup.mem_iInf]

theorem div_mem_chartRing (x : ι → Ω) (i j : ι) :
    x j / x i ∈ chartRing o x i :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem exists_pow_mul_mem_chartRing (x : ι → Ω) (i j : ι) (hi : x i ≠ 0)
    {a : Ω} (ha : a ∈ chartRing o x i) :
    ∃ m : ℕ, (x i / x j) ^ m * a ∈ chartRing o x j := by
  have hij : x i / x j ∈ chartRing o x j := div_mem_chartRing x j i
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have : x i / x j * (x k / x i) = x k / x j := by field_simp
    rw [pow_one, this]
    exact div_mem_chartRing x j k
  | algebraMap r =>
    exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y + z) =
        (x i / x j) ^ n * ((x i / x j) ^ m * y) + (x i / x j) ^ m * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hij _) hm) (mul_mem (pow_mem hij _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y * z) = ((x i / x j) ^ m * y) * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact mul_mem hm hn

variable (o)

def lineLat (x : ι → Ω) (d : ℕ) (i : ι) : AddSubgroup Ω :=
  ((Subalgebra.toSubmodule (chartRing o x i)).map (LinearMap.mulRight o (x i ^ d))).toAddSubgroup

variable {o}

theorem mem_lineLat (x : ι → Ω) (d : ℕ) (i : ι) (e : Ω) :
    e ∈ lineLat o x d i ↔ ∃ a ∈ chartRing o x i, a * x i ^ d = e := by
  simp [lineLat]

variable (o)

def lineBundle (x : ι → Ω) (d : ℕ) : ChartBundle o x 1 Ω where
  lat := lineLat o x d
  stable i a ha e he := by
    obtain ⟨c, hc, rfl⟩ := (mem_lineLat x d i e).1 he
    refine (mem_lineLat x d i _).2 ⟨a * c, mul_mem ha hc, ?_⟩
    rw [smul_eq_mul, mul_assoc]
  frame i hi := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    refine ⟨fun _ => x i ^ d, ?_, ?_, ?_⟩
    · rw [linearIndependent_unique_iff]
      exact pow_ne_zero _ hi
    · rw [Set.range_const]
      exact Ideal.span_singleton_eq_top.2 (isUnit_iff_ne_zero.2 (pow_ne_zero _ hi))
    · intro e
      rw [mem_lineLat]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨fun _ => a, fun _ => ha, by simp⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a 0, ha 0, by simp⟩
  overlap i j hi hj e he := by
    obtain ⟨a, ha, rfl⟩ := (mem_lineLat x d i e).1 he
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_chartRing x i j hi ha
    refine ⟨m, (mem_lineLat x d j _).2 ⟨(x i / x j) ^ m * a * (x i / x j) ^ d,
      mul_mem hm (pow_mem (div_mem_chartRing x j i) _), ?_⟩⟩
    rw [smul_eq_mul, div_pow, div_pow]
    field_simp

end Chart

end ReciprocityTheory.ChartRestriction.G.Geo
