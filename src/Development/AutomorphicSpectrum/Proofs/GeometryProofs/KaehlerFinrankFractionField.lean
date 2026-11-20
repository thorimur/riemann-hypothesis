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
import Mathlib.RingTheory.Henselian
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

open TensorProduct

namespace GlobalTheory.CompanionTheory.Ggeo

theorem finrank_kaehler_fractionRing_eq_of_basis
    (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] (m : ℕ) (w : Fin m → T)
    (hli : LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)))
    (hspan : Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤) :
    Module.finrank L (KaehlerDifferential K L) = m := by
  haveI : Algebra.FormallyEtale T L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors T)
  haveI : Algebra.FormallyUnramified S K :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors S)
  haveI : Subsingleton (KaehlerDifferential S K) :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have hinj : Function.Injective (KaehlerDifferential.map S K L L) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map S K L x).1 hx
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  let e : KaehlerDifferential S L ≃ₗ[L] KaehlerDifferential K L :=
    LinearEquiv.ofBijective (KaehlerDifferential.map S K L L)
      ⟨hinj, KaehlerDifferential.map_surjective S K L⟩
  let b : Module.Basis (Fin m) T (KaehlerDifferential S T) := Module.Basis.mk hli hspan.ge
  let b' : Module.Basis (Fin m) L (KaehlerDifferential K L) :=
    ((Algebra.TensorProduct.basis L b).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale S T L)).map e
  simpa using Module.finrank_eq_card_basis b'

end GlobalTheory.CompanionTheory.Ggeo
