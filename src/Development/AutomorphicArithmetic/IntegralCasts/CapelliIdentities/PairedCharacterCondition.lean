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
import Mathlib.Topology.Sheaves.Init

noncomputable def UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale :
    Prop :=
    ∀ (K : Type) [inst : Field K] [NumberField K] (V : Type) [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
      (M : Submodule (NumberField.RingOfIntegers K) V),
      Submodule.span K (↑M : Set V) = ⊤ → ∀ (f : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ (↑m : K) • f ∈ M

theorem UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale :
    UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale := by
  intro K _ _ V _ _ _ _ M hM f
  have key : ∀ (c : K), IsIntegral ℤ c → ∀ x ∈ M, c • x ∈ M := by
    intro c hc x hx
    obtain ⟨r, rfl⟩ : ∃ r : NumberField.RingOfIntegers K, algebraMap _ K r = c := ⟨⟨c, hc⟩, rfl⟩
    rw [algebraMap_smul]
    exact M.smul_mem r hx
  have hint : ∀ n : ℤ, IsIntegral ℤ (n : K) := fun n => isIntegral_algebraMap (R := ℤ) (x := n)
  have hf : f ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℤ) : K) • (x + y) = (b : K) • ((a : K) • x) + (a : K) • ((b : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (b : K)]
    rw [e]
    exact M.add_mem (key _ (hint b) _ hx) (key _ (hint a) _ hy)
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have halg : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨b, hb, hc⟩ := halg.exists_integral_multiple
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℤ) : K) • (c • x) = (b • c) • ((a : K) • x) := by
      rw [smul_smul, smul_smul, Int.cast_mul, zsmul_eq_mul]
      congr 1
      ring
    rw [e]
    exact key _ hc _ hx
