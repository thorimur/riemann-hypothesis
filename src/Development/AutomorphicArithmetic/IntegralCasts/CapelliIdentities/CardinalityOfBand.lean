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
import Std.Tactic.BVDecide.Normalize.Prop

noncomputable def UpperTheory.Reformulated.B.CardinalityOfBand.band :
    (m : Nat) → Nat → Nat → Fin m → Bool :=
    fun (m a b : Nat) (i : Fin m) ↦
      @Decidable.decide (And (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b))
        (@instDecidableAnd (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b)
          (a.decLe (@Fin.val m i)) ((@Fin.val m i).decLt b))

theorem UpperTheory.Reformulated.B.CardinalityOfBand.card_band :
    ∀ (m a b : Nat),
      @LE.le Nat instLENat b m →
        @Eq Nat (@Finset.card (Fin m) {i : Fin m | @Eq Bool (UpperTheory.Reformulated.B.CardinalityOfBand.band m a b i) Bool.true})
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) b a) := by
  intro m a b hb
  rw [← Nat.card_Ico a b, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_Ico, UpperTheory.Reformulated.B.CardinalityOfBand.band, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    exact ⟨⟨x, lt_of_lt_of_le hx.2 hb⟩, hx, rfl⟩
