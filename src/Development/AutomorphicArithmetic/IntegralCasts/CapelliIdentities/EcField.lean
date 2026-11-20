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
import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh13.Plc :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh13.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh13.Emb :
    {F : Type} → [inst : Field F] → [NumberField F] → (l : ℕ) → [Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.Qh13.Plc F → Type :=
    fun {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact (Nat.Prime l)] (w : UpperTheory.Reformulated.B.Qh13.Plc F) ↦
      { j : IsDedekindDomain.HeightOneSpectrum.adicCompletion F w →+* UpperTheory.Reformulated.B.Qh13.Qbar l //
        Continuous (⇑j : IsDedekindDomain.HeightOneSpectrum.adicCompletion F w → UpperTheory.Reformulated.B.Qh13.Qbar l) }

theorem UpperTheory.Reformulated.B.Qh13.ec_field :
    ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {l : ℕ} [inst_2 : Fact (Nat.Prime l)]
      {w : UpperTheory.Reformulated.B.Qh13.Plc L} (j : UpperTheory.Reformulated.B.Qh13.Emb l w),
      ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
        FiniteDimensional ℚ_[l] ↥K ∧
          ∀ (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion L w),
            ((↑j : IsDedekindDomain.HeightOneSpectrum.adicCompletion L w →+* UpperTheory.Reformulated.B.Qh13.Qbar l) :
                  IsDedekindDomain.HeightOneSpectrum.adicCompletion L w → UpperTheory.Reformulated.B.Qh13.Qbar l)
                x ∈
              K := by
  intro L _ _ l _ w j
  obtain ⟨j, hj⟩ := j
  let f : L →+* PadicAlgCl l :=
    j.comp (algebraMap L (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w))
  let b := Module.finBasis ℚ L
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) :=
    IntermediateField.adjoin ℚ_[l] (Set.range fun i => f (b i))
  have hK : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hf : ∀ y : L, f y ∈ K := by
    intro y
    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem K _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  have hc : IsClosed (K : Set (PadicAlgCl l)) :=
    haveI : FiniteDimensional ℚ_[l] K.toSubalgebra.toSubmodule := hK
    K.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  refine ⟨K, hK, fun x => ?_⟩
  exact (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap L w).induction_on x
    (hc.preimage hj) hf
