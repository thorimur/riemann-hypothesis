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
import Mathlib.FieldTheory.IsAlgClosed.Classification
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

noncomputable section
open NumberField IsDedekindDomain Cardinal
open scoped nonZeroDivisors

namespace ReciprocityTheory.ChartRestriction.B3

theorem iop_extEmb {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  let : Algebra R K := f.toAlgebra
  let : Algebra R L := g.toAlgebra
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' R K
  obtain ⟨κ, w, hw⟩ := exists_isTranscendenceBasis' R L
  have h1 : #K = #ι := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' v hv hR hK
  have h2 : #L = #κ :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' w hw hR (hKL ▸ hK)
  obtain ⟨e⟩ := Cardinal.eq.1 (h1.symm.trans (hKL.trans h2))
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis v hv
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis w hw
  let e' : Algebra.adjoin R (Set.range v) ≃ₐ[R] Algebra.adjoin R (Set.range w) :=
    (hv.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv R e)).trans hw.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv K L e'.toRingEquiv, fun r => ?_⟩
  have hf : f r = algebraMap R K r := rfl
  have hg : g r = algebraMap R L r := rfl
  rw [hf, hg, IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range v)) K,
    IsAlgClosure.equivOfEquiv_algebraMap]
  have : e'.toRingEquiv (algebraMap R _ r) = algebraMap R _ r := e'.commutes r
  rw [this, ← IsScalarTower.algebraMap_apply]

end ReciprocityTheory.ChartRestriction.B3
