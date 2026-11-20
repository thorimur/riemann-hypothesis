import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
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
import Std.Tactic.BVDecide.Normalize.Prop

namespace GlobalTheory

theorem posquad_finite : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (q : X → ℤ), (∀ a, q (-a) = q a) → (∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b)) → (∀ a, a ≠ 0 → 1 ≤ q a) → ∀ N : ℤ, {a | q a ≤ N}.Finite := by
  intro X _ _ q hneg hcube hpos N
  have h0 : q 0 = 0 := by
    have := hcube 0 0 0
    simp only [add_zero] at this
    linarith
  have hnn : ∀ a, 0 ≤ q a := by
    intro a
    by_cases ha : a = 0
    · simp [ha, h0]
    · linarith [hpos a ha]
  let B : X → X → ℤ := fun a b => q (a + b) - q a - q b
  have Bsymm : ∀ a b, B a b = B b a := by
    intro a b; simp only [B, add_comm a b]; ring
  have Badd : ∀ a a' b, B (a + a') b = B a b + B a' b := by
    intro a a' b
    simp only [B]
    linarith [hcube a a' b]
  let L : X → (X →+ ℤ) := fun b => AddMonoidHom.mk' (fun a => B a b) (fun a a' => Badd a a' b)
  have L_apply : ∀ a b, L b a = B a b := fun _ _ => rfl
  have Bdiag : ∀ a, B a a = 2 * q a := by
    intro a
    have h := hcube a (-a) a
    simp only [add_neg_cancel, neg_add_cancel, zero_add, hneg, h0] at h
    show q (a + a) - q a - q a = 2 * q a
    linarith
  have Bbound : ∀ a s, |B a s| ≤ q a + q s := by
    intro a s
    have h1 : B a s = q (a + s) - q a - q s := rfl
    have h2 : B (-a) s = q (-a + s) - q (-a) - q s := rfl
    have h3 : B (-a) s = - B a s := by
      rw [← L_apply, ← L_apply, map_neg]
    rw [hneg] at h2
    have := hnn (a + s)
    have := hnn (-a + s)
    rw [abs_le]; constructor <;> linarith
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  have hzero : ∀ c, (∀ i ∈ S, B c i = 0) → c = 0 := by
    intro c hc
    have hle : Submodule.span ℤ (S : Set X) ≤ (L c).ker.toIntSubmodule := by
      rw [Submodule.span_le]
      intro x hx
      change (L c) x = 0
      rw [L_apply, Bsymm]; exact hc x hx
    have hc' : c ∈ (L c).ker.toIntSubmodule := hle (hS ▸ Submodule.mem_top)
    change (L c) c = 0 at hc'
    rw [L_apply, Bdiag] at hc'
    by_contra hne
    have := hpos c hne
    omega
  let φ : X → (S → ℤ) := fun a i => B a i
  have φinj : Function.Injective φ := by
    intro a a' h
    have : a - a' = 0 := by
      apply hzero
      intro i hi
      have hi' := congrFun h ⟨i, hi⟩
      simp only [φ] at hi'
      rw [← L_apply, map_sub, L_apply, L_apply, hi', sub_self]
    exact sub_eq_zero.mp this
  have hfin : (Set.pi Set.univ (fun i : S => Set.Icc (-(N + q i)) (N + q i))).Finite :=
    Set.Finite.pi (fun i => Set.finite_Icc _ _)
  refine (hfin.preimage φinj.injOn).subset ?_
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  have := Bbound a i
  rw [abs_le] at this
  simp only [φ]
  constructor <;> linarith

end GlobalTheory
