import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
open NumberField
open scoped TensorProduct NNReal

theorem UpperTheory.WildB.dualFamily :
    ∀ (E : Type) [Field E] [NumberField E] (d : 𝓞 E), d ∈ differentIdeal ℤ (𝓞 E) → d ≠ 0 → ∃ (n : ℕ) (a b : Fin n → 𝓞 E), (∀ x : E, ∑ j, Algebra.trace ℚ E (x * (b j : E) / (d : E)) • (a j : E) = x) ∧ (∀ x : E, ∑ j, Algebra.trace ℚ E (x * (a j : E) / (d : E)) • (b j : E) = x) ∧ ∀ (x : 𝓞 E) (i j : Fin n), ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ E ((x : E) * (a j : E) * (b i : E) / (d : E)) := by
  intro E _ _ d hd hd0
  classical
  let B := integralBasis E
  have hrep : ∀ (x : E) i, B.repr x i = Algebra.trace ℚ E (x * B.traceDual i) := fun x i => by
    have h := B.traceDual.traceDual_repr_apply x i
    rw [B.traceDual_traceDual, Algebra.traceForm_apply] at h
    exact h
  have hrep' : ∀ (x : E) i, B.traceDual.repr x i = Algebra.trace ℚ E (x * B i) := fun x i => by
    have h := B.traceDual_repr_apply x i
    rw [Algebra.traceForm_apply] at h
    exact h
  have hc : ∀ i, ∃ c : 𝓞 E, (c : E) = B.traceDual i * d := fun i => by
    have hx : B.traceDual i ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
      rw [FractionalIdeal.mem_dual (by simp)]
      intro a ha
      obtain ⟨y, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      refine ⟨(RingOfIntegers.basis E).repr y i, ?_⟩
      rw [← integralBasis_repr_apply]
      have h := B.traceDual.traceDual_repr_apply (algebraMap (𝓞 E) E y) i
      rw [B.traceDual_traceDual, Algebra.traceForm_apply, mul_comm] at h
      exact h
    have hdd : (d : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
    rw [coeIdeal_differentIdeal ℤ ℚ] at hdd
    have hm := FractionalIdeal.mul_mem_mul hx hdd
    rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (by simp))] at hm
    exact (FractionalIdeal.mem_one_iff _).1 hm
  choose c hc using hc
  have hdE : (d : E) ≠ 0 := fun h => hd0 (RingOfIntegers.ext h)
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm
  have ha : ∀ i, ((RingOfIntegers.basis E i : 𝓞 E) : E) = B i := fun i =>
    (integralBasis_apply E i).symm
  have hdiv : ∀ (y : E) i, y * (c i : E) / (d : E) = y * B.traceDual i := fun y i => by
    rw [hc, ← mul_assoc, mul_div_cancel_right₀ _ hdE]
  refine ⟨_, fun j => RingOfIntegers.basis E (e j), fun j => c (e j), fun x => ?_, fun x => ?_,
    fun x i j => ?_⟩
  · simp only [hdiv, ha, ← hrep]
    rw [e.sum_comp (fun i => B.repr x i • B i)]
    exact B.sum_repr x
  · have h1 : ∀ i, Algebra.trace ℚ E (x * B i / (d : E)) • (c i : E)
        = (B.traceDual.repr (x / d) i • B.traceDual i) * d := fun i => by
      rw [hrep', hc, smul_mul_assoc, mul_div_right_comm]
    simp only [ha, h1]
    rw [e.sum_comp (fun i => (B.traceDual.repr (x / d) i • B.traceDual i) * (d : E)),
      ← Finset.sum_mul, B.traceDual.sum_repr, div_mul_cancel₀ _ hdE]
  · refine ⟨(RingOfIntegers.basis E).repr (x * RingOfIntegers.basis E (e j)) (e i), ?_⟩
    rw [hdiv, ← hrep]
    have h := integralBasis_repr_apply E (x * RingOfIntegers.basis E (e j)) (e i)
    rw [map_mul] at h
    exact h.symm
