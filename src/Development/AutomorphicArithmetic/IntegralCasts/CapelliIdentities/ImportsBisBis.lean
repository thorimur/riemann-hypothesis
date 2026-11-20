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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

noncomputable def UpperTheory.Reformulated.B.DYhc9.IsLat :
    {E : Type} → [inst : Field E] → {N : ℕ} → Submodule (NumberField.RingOfIntegers E) (Fin N → E) → Prop :=
    fun {E : Type} [Field E] {N : ℕ} (Λ : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) ↦
      Λ.FG ∧ Submodule.span E (↑Λ : Set (Fin N → E)) = ⊤

private theorem UpperTheory.Reformulated.B.DYhc9.exists_denom {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  have halg : IsAlgebraic ℤ a := by
    have : Algebra.IsAlgebraic ℤ E :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).mpr inferInstance
    exact Algebra.IsAlgebraic.isAlgebraic a
  obtain ⟨r, hr, hint⟩ := halg.exists_integral_multiple
  have hint' : IsIntegral ℤ ((r : E) * a) := by simpa [zsmul_eq_mul] using hint
  refine ⟨r.natAbs, Int.natAbs_ne_zero.mpr hr, ?_⟩
  rcases Int.natAbs_eq r with h | h
  · have : ((r.natAbs : E)) = (r : E) := by
      conv_rhs => rw [h]
      simp
    rwa [this]
  · have : ((r.natAbs : E)) = -(r : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]
    exact hint'.neg

theorem UpperTheory.Reformulated.B.DYhc9.main :
    ∀ {E : Type} [inst : Field E] [NumberField E] {N : ℕ} {Λ : Submodule (NumberField.RingOfIntegers E) (Fin N → E)},
      UpperTheory.Reformulated.B.DYhc9.IsLat Λ → ∀ (x : Fin N → E), ∃ (m : ℕ), m ≠ (0 : ℕ) ∧ (↑m : E) • x ∈ Λ := by
  intro E _ _ N Λ h x
  have hx : x ∈ Submodule.span E (Λ : Set (Fin N → E)) := by
    rw [h.2]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hmy⟩ := hy
    obtain ⟨n, hn, hnz⟩ := hz
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have key : ((m * n : ℕ) : E) • (y + z) = n • ((m : E) • y) + m • ((n : E) • z) := by
      ext i
      simp
      ring
    rw [key]
    exact Λ.add_mem (nsmul_mem hmy n) (nsmul_mem hnz m)
  | smul a y _ hy =>
    obtain ⟨m, hm, hmy⟩ := hy
    obtain ⟨d, hd, hint⟩ := UpperTheory.Reformulated.B.DYhc9.exists_denom a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    obtain ⟨b, hb⟩ : ∃ b : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E b = (d : E) * a :=
      ⟨_, IsIntegralClosure.algebraMap_mk' _ _ hint⟩
    have key : ((d * m : ℕ) : E) • (a • y) = b • ((m : E) • y) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Algebra.smul_def, hb]
      push_cast
      ring
    rw [key]
    exact Λ.smul_mem _ hmy
