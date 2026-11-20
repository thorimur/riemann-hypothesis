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
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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

namespace GlobalTheory.TendstoOfIntegrals

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology

theorem tendsto_of_forall_integral {L : Type} [Field L] [NumberField L] {ι : Type} {l : Filter ι}
    (f : ι → FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (b : FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (hf : ∀ (i : ι) (v : HeightOneSpectrum (NumberField.RingOfIntegers L)),
      (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hb : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      (b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hl : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      Tendsto (fun i ↦ (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) →
        a.adicCompletion L) v) l
        (𝓝 ((b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v))) :
    Tendsto f l (𝓝 b) := by

  let A : (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → Set (v.adicCompletion L) :=
    fun v ↦ (v.adicCompletionIntegers L : Set (v.adicCompletion L))
  let g : ι → (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → A v :=
    fun i v ↦ ⟨_, hf i v⟩
  let c : (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → A v := fun v ↦ ⟨_, hb v⟩
  have hg : Tendsto g l (𝓝 c) :=
    tendsto_pi_nhds.2 fun v ↦ tendsto_subtype_rng.2 (hl v)
  have hemb := RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦ v.adicCompletion L)
    (A := A) (𝓕 := cofinite)
  exact (hemb.continuous.tendsto c).comp hg

end GlobalTheory.TendstoOfIntegrals

theorem GlobalTheory.TendstoOfIntegrals.target_check : ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {ι : Type} {l : Filter ι} (f : ι → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers L) L) (b : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers L) L), (∀ (i : ι) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), (f i : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers L v) → (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), (b : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers L v) → (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), Filter.Tendsto (fun (i : ι) ↦ (f i : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v) l (nhds ((b : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v))) → Filter.Tendsto f l (nhds b) := by
  intro L _ _ ι l f b hf hb hl
  exact GlobalTheory.TendstoOfIntegrals.tendsto_of_forall_integral f b hf hb hl
