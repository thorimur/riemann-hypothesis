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
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
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

universe u_1 u_2

namespace GlobalTheory.IrreducibleMembership

theorem mem_of_irreducible {K : Type u_1} {V : Type u_2} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hf1 : f = 1 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hf1]
    exact S.one_mem
  · have hso : IsSimpleOrder (Submodule S V) := by
      refine ⟨fun N => ?_⟩
      have hN := h (N.restrictScalars K) fun g hg v hv => by
        have hmem : (⟨g, hg⟩ : S) • v ∈ N := N.smul_mem _ hv
        exact hmem
      rcases hN with hN | hN
      · left
        exact (Submodule.restrictScalars_eq_bot_iff K S V).1 hN
      · right
        exact (Submodule.restrictScalars_eq_top_iff K S V).1 hN
    have hsimp : IsSimpleModule S V := ⟨⟩
    have hbij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K
    let F : Module.End (Module.End S V) V :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := fun g v => by
          obtain ⟨c, hc⟩ := hbij.2 g
          rw [← hc]
          simp }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
    have hfr : f = (r : Module.End K V) := by
      refine b.ext fun i => ?_
      have := hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))
      exact this
    rw [hfr]
    exact r.2

end GlobalTheory.IrreducibleMembership
