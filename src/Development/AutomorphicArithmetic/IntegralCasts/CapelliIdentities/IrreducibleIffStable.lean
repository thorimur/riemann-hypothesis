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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.StableSubmoduleBotOrTopOfSpanEqTop.irrIff_stable :
    ∀ {H K : Type} [inst : Group H] [inst_1 : Field K] {n : ℕ}
    (r : H →* Matrix (Fin n) (Fin n) K),
    Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K)) = ⊤ →
      ∀ (W : Submodule K (Fin n → K)),
        (∀ (g : H), ∀ v ∈ W, ((r : H → Matrix (Fin n) (Fin n) K) g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro H K _ _ n r hspan W hW
  have hall : ∀ (A : Matrix (Fin n) (Fin n) K), ∀ v ∈ W, A.mulVec v ∈ W := by
    intro A v hv
    have hA : A ∈ Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hW g v hv
    | zero => rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_mulVec]; exact W.smul_mem c hx
  by_cases hb : W = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : v i ≠ 0 := hi
    rw [eq_top_iff]
    intro w _
    have h := hall (Matrix.of fun a b => if b = i then w a / v i else 0) v hv
    have e : (Matrix.of fun a b => if b = i then w a / v i else 0 :
        Matrix (Fin n) (Fin n) K).mulVec v = w := by
      funext a
      simp [Matrix.mulVec, dotProduct, hi']
    rwa [e] at h
