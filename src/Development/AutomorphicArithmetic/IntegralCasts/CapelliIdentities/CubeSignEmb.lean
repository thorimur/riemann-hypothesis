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

noncomputable def UpperTheory.Reformulated.B.Qh71.cubeSign :
    {ι : Type} → [LinearOrder ι] → Finset ι → ι → ℤ :=
    fun {ι : Type} [LinearOrder ι] (t : Finset ι) (i : ι) ↦ (-1 : ℤ) ^ {x ∈ t | x < i}.card

theorem UpperTheory.Reformulated.B.Qh71.cubeSign_emb :
    ∀ {κ : Type} [inst : LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n) (k : Fin n),
      UpperTheory.Reformulated.B.Qh71.cubeSign t ((t.orderEmbOfFin h : Fin n → κ) k) = (-1 : ℤ) ^ (↑k : ℕ) := by
  intro κ _ t n h k
  have key : {x ∈ t | x < t.orderEmbOfFin h k}
      = (Finset.Iio k).map (t.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      have hr : x ∈ Set.range (t.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨j, rfl⟩ := hr
      exact ⟨j, (t.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem t h j, (t.orderEmbOfFin h).lt_iff_lt.mpr hj⟩
  unfold UpperTheory.Reformulated.B.Qh71.cubeSign
  rw [key, Finset.card_map, Fin.card_Iio]
