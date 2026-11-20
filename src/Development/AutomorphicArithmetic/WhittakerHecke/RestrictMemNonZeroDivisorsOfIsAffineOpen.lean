import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem UpperTheory.restrict_mem_nonZeroDivisors_of_isAffineOpen :
    ∀ {W : Scheme.{0}} {V O : W.Opens}, IsAffineOpen V → ∀ (h : O ≤ V) (t : Γ(W, V)), t ∈ nonZeroDivisors Γ(W, V) →
        W.presheaf.map (homOfLE h).op t ∈ nonZeroDivisors Γ(W, O) := by
  intro W V O hV h t ht
  rw [mem_nonZeroDivisors_iff_right] at ht ⊢
  intro s hs
  refine TopCat.Presheaf.section_ext W.sheaf O s 0 (fun x hx => ?_)
  rw [map_zero]
  have hxV : x ∈ V := h hx
  algebraize [(W.presheaf.germ V x hxV).hom]
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have hloc := IsLocalization.nonZeroDivisors_le_comap (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (W.presheaf.stalk x) (mem_nonZeroDivisors_iff_right.mpr ht)
  rw [Submonoid.mem_comap, RingHom.algebraMap_toAlgebra, mem_nonZeroDivisors_iff_right] at hloc
  apply hloc
  have e := congrArg (W.presheaf.germ O x hx).hom hs
  rw [map_mul, map_zero, TopCat.Presheaf.germ_res_apply] at e
  exact e
