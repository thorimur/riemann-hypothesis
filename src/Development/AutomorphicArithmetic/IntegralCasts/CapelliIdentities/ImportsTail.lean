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
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.DYha5.main :
    ∀ {Ω Ω₀ F F₀ : Type} [inst : Field Ω] [inst_1 : Field Ω₀] [inst_2 : AddCommGroup F] [inst_3 : _root_.Module Ω F]
      [inst_4 : AddCommGroup F₀] [inst_5 : _root_.Module Ω₀ F₀] (i : Ω₀ →+* Ω) (ι : F₀ →+ F),
      (∀ (a : Ω₀) (e : F₀), (ι : F₀ → F) (a • e) = (i : Ω₀ → Ω) a • (ι : F₀ → F) e) →
        ∀ (W : Subring Ω) (A : Subring Ω₀),
          (∀ a ∈ A, (i : Ω₀ → Ω) a ∈ W) →
            ∀ (T : Set F₀),
              Submodule.span (↥W) ((⇑ι : F₀ → F) '' (↑(Submodule.span (↥A) T) : Set F₀)) =
                Submodule.span (↥W) ((⇑ι : F₀ → F) '' T) := by
  intro Ω Ω₀ F F₀ _ _ _ _ _ _ i ι hι W A hA T
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span (↥A) T := hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ (hy ‹_›) (hz ‹_›)
    | smul a y _ hy =>
      have h1 : ι (a • y) = (⟨i a, hA a a.2⟩ : ↥W) • ι y := hι (a : Ω₀) y
      rw [h1]
      exact Submodule.smul_mem _ _ (hy ‹_›)
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
