import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
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

open CategoryTheory UpperTheory.V.KH

private theorem group_homology_long_exact (k G : Type) [CommRing k] [Group G] (A B C : Rep k G)
    (f : A ⟶ B) (g : B ⟶ C) (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom)
    (hg : Function.Surjective g.hom) (j : ℕ) :
      (∃ (u : groupHomology A j →+ groupHomology B j) (v : groupHomology B j →+ groupHomology C j),
        Function.Exact u v) ∧
      (∃ (u : groupHomology B (j + 1) →+ groupHomology C (j + 1))
        (v : groupHomology C (j + 1) →+ groupHomology A j), Function.Exact u v) := by
  have h0 : f ≫ g = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact hfg.apply_apply_eq_zero x
  let X : ShortComplex (Rep k G) := ShortComplex.mk f g h0
  have hex : X.Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful X (forget₂ (Rep k G) (ModuleCat k))]
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg
  have hX : X.ShortExact :=
    ShortComplex.ShortExact.mk' hex ((Rep.mono_iff_injective f).2 hf)
      ((Rep.epi_iff_surjective g).2 hg)
  have h2 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (groupHomology.mapShortComplex₂_exact hX j)
  have h3 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (groupHomology.mapShortComplex₃_exact hX (i := j + 1) (j := j) rfl)
  exact ⟨⟨(groupHomology.mapShortComplex₂ X j).f.hom.toAddMonoidHom,
      (groupHomology.mapShortComplex₂ X j).g.hom.toAddMonoidHom, h2⟩,
    ⟨(groupHomology.mapShortComplex₃ hX (i := j + 1) (j := j) rfl).f.hom.toAddMonoidHom,
      (groupHomology.mapShortComplex₃ hX (i := j + 1) (j := j) rfl).g.hom.toAddMonoidHom, h3⟩⟩

theorem UpperTheory.V.KH.les :
    ∀ (G : Type) [Group G] (A B C : Rep ℤ G) (f : A ⟶ B) (g : B ⟶ C),
      Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom → ∀ j : ℕ,
      (∃ (u : groupHomology A j →+ groupHomology B j) (v : groupHomology B j →+ groupHomology C j),
        Function.Exact u v) ∧
      (∃ (u : groupHomology B (j + 1) →+ groupHomology C (j + 1))
        (v : groupHomology C (j + 1) →+ groupHomology A j), Function.Exact u v) := by
  intro G _ A B C f g hf hfg hg j
  exact group_homology_long_exact ℤ G A B C f g hf hfg hg j
