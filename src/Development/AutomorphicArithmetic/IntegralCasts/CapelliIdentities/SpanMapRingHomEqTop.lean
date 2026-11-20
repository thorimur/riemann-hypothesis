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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.Qe1.span_map_ringHom_eq_top :
    ∀ {k K G ι : Type} [inst : Field k] [inst_1 : Field K]
    [Fintype ι] [DecidableEq ι] (φ : k →+* K) (f : G → Matrix ι ι k),
    Submodule.span k (Set.range f) = ⊤ → Submodule.span K (Set.range fun (g : G) ↦ (f g).map (⇑φ : k → K)) = ⊤ := by
  intro k K G ι _ _ _ _ φ f h
  have key : ∀ M : Matrix ι ι k, M ∈ Submodule.span k (Set.range f) →
      M.map (⇑φ : k → K) ∈
        Submodule.span K (Set.range fun (g : G) ↦ (f g).map (⇑φ : k → K)) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact Submodule.subset_span ⟨g, rfl⟩
    | zero =>
      have e : (0 : Matrix ι ι k).map (⇑φ : k → K) = 0 := by
        ext i j
        simp
      rw [e]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have e : (x + y).map (⇑φ : k → K) = x.map (⇑φ : k → K) + y.map (⇑φ : k → K) := by
        ext i j
        simp
      rw [e]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have e : (a • x).map (⇑φ : k → K) = φ a • x.map (⇑φ : k → K) := by
        ext i j
        simp
      rw [e]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro N _
  rw [Matrix.matrix_eq_sum_single N]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j (N i j)
      = N i j • (Matrix.single i j (1 : k)).map (⇑φ : k → K) := by
    ext a b
    by_cases hab : i = a ∧ j = b <;> simp [Matrix.single, hab]
  rw [e]
  exact Submodule.smul_mem _ _ (key _ (h ▸ Submodule.mem_top))
