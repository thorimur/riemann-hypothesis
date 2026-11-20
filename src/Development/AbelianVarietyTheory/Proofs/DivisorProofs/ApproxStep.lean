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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.FixedPointApproximation

noncomputable def approx {B : Type} [CommRing B] (q : B) (σ : B →+* B) (w : B) : ℕ → B
  | 0 => 0
  | n + 1 => -w + q * σ (approx q σ w n)

theorem approx_step {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B) (n : ℕ) :
    q ^ n ∣ approx q σ w (n + 1) - approx q σ w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨σ t, ?_⟩
    have e : approx q σ w (n + 1 + 1) - approx q σ w (n + 1) =
        q * σ (approx q σ w (n + 1) - approx q σ w n) := by
      rw [map_sub]
      show -w + q * σ (approx q σ w (n + 1)) - (-w + q * σ (approx q σ w n)) = _
      ring
    rw [e, ht, map_mul, map_pow, hq]
    ring

theorem approx_dvd {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B)
    (m n : ℕ) (h : m ≤ n) : q ^ m ∣ approx q σ w m - approx q σ w n := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have h2 : q ^ m ∣ approx q σ w (n + 1) - approx q σ w n :=
      (pow_dvd_pow q hmn).trans (approx_step q σ hq w n)
    have e : approx q σ w m - approx q σ w (n + 1) =
        (approx q σ w m - approx q σ w n) - (approx q σ w (n + 1) - approx q σ w n) := by ring
    rw [e]
    exact dvd_sub ih h2

theorem smodEq_iff {B : Type} [CommRing B] (q : B) (n : ℕ) (x y : B) :
    x ≡ y [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule B B)] ↔ q ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem exists_fixed {B : Type} [inst : CommRing B] (q : B)
    [h : IsAdicComplete (Ideal.span {q}) B] (σ : B →+* B) (hq : σ q = q) (w : B) :
    ∃ c : B, c = -w + q * σ c := by
  obtain ⟨c, hc⟩ := h.toIsPrecomplete.prec (f := approx q σ w) fun {m n} hmn =>
    (smodEq_iff q m _ _).mpr (approx_dvd q σ hq w m n hmn)
  refine ⟨c, ?_⟩
  have hd : ∀ n, q ^ n ∣ c - (-w + q * σ c) := by
    intro n
    have h1 : q ^ n ∣ approx q σ w n - c := (smodEq_iff q n _ _).mp (hc n)
    have h2 : q ^ (n + 1) ∣ approx q σ w (n + 1) - c := (smodEq_iff q (n + 1) _ _).mp (hc (n + 1))
    obtain ⟨t, ht⟩ := h1
    have e : c - (-w + q * σ c) = -(approx q σ w (n + 1) - c) + q * σ (approx q σ w n - c) := by
      rw [map_sub]
      show _ = -((-w + q * σ (approx q σ w n)) - c) + q * (σ (approx q σ w n) - σ c)
      ring
    rw [e, ht, map_mul, map_pow, hq]
    exact dvd_add (dvd_neg.mpr ((pow_dvd_pow q (Nat.le_succ n)).trans h2)) ⟨q * σ t, by ring⟩
  have h0 := h.toIsHausdorff.haus (c - (-w + q * σ c)) fun n =>
    (smodEq_iff q n _ _).mpr (by simpa using hd n)
  exact sub_eq_zero.mp h0

end GlobalTheory.FixedPointApproximation
