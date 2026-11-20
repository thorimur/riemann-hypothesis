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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
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

namespace GlobalTheory

theorem isReduced_of_smooth_over_field (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] : IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  by_contra h0
  obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal (Ideal.span {a}).annihilator fun h =>
    h0 ((one_smul A a).symm.trans ((Submodule.mem_annihilator_span_singleton a 1).1 (h ▸ Submodule.mem_top)))
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let P := MvPolynomial (Fin n) K
  have : IsReduced (TensorProduct P (FractionRing P) (Localization.Away f)) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing P) _
  have : IsReduced (Localization.Away f) := isReduced_of_injective _
    (Algebra.TensorProduct.includeRight_injective (A := FractionRing P) (IsFractionRing.injective P _))
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) a).1
    (ha.map (algebraMap A (Localization.Away f))).eq_zero
  exact hf (hp.isPrime.mem_of_pow_mem N (hI ((Submodule.mem_annihilator_span_singleton a _).2 hN)))

end GlobalTheory
