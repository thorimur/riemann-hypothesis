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
import Mathlib.Order.CompletePartialOrder
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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem isPrime_map_quotient_localization {R : Type*} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    (hWm : W ≤ m) (hIW : I ≤ W) :
    (W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m)))).IsPrime := by
  rw [← Ideal.map_map]
  have hd : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) W ‹_› hd
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact Ideal.map_mono hIW)

def LocalizeQuotientStages.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime], W ≤ m → I ≤ W →
    ∀ (P : Ideal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))) [P.IsPrime],
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) = P →
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) =
        Module.length (Localization.AtPrime W)
          (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W)))

end

end GroundTheory.Heights₂.Heights
