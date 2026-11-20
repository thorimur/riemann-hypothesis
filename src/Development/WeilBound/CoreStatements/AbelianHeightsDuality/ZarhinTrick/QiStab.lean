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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

theorem exists_stable_pow {K H : Type} [Field K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (I : Ideal H) : ∃ (k : ℕ) (e : H), IsIdempotentElem e ∧ I ^ k = Ideal.span {e} ∧ ∀ j, k ≤ j → I ^ j = I ^ k := by
  haveI : IsArtinianRing H := isArtinian_of_tower K inferInstance
  haveI : IsNoetherianRing H := isNoetherian_of_tower K inferInstance
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := H) (M := H)
    ⟨fun n => OrderDual.toDual (I ^ n), fun a b h => Ideal.pow_le_pow_right h⟩
  have hst : ∀ j, n ≤ j → I ^ j = I ^ n := fun j hj => congrArg OrderDual.ofDual (hn j hj).symm
  have hidem : IsIdempotentElem (I ^ n) := by
    unfold IsIdempotentElem
    rw [← pow_add]
    exact hst (n + n) (by omega)
  obtain ⟨e, he, hI⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).1 hidem
  exact ⟨n, e, he, hI.trans Ideal.submodule_span_eq, hst⟩

end PositivityTheory.PrwZar.Qi
