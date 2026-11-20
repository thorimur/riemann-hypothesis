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
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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

open Polynomial in
theorem UpperTheory.Reformulated.B.DvdOfAeval.dvd_of_aeval :
    ∀ {K : Type} [inst : Field K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K),
    g.charpoly.Separable →
      ∀ (p : Polynomial K),
        (Polynomial.aeval g : Polynomial K → Matrix (Fin n) (Fin n) K) p = (0 : Matrix (Fin n) (Fin n) K) →
          g.charpoly ∣ p := by
  intro K _ n g hsep p hp
  by_cases hp0 : p = 0
  · simp [hp0]
  let L := AlgebraicClosure K
  let φ : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) L :=
    (Algebra.ofId K L).mapMatrix
  have hchar : (φ g).charpoly = g.charpoly.map (algebraMap K L) := by
    have := Matrix.charpoly_map g (algebraMap K L)
    exact this
  have hzero : aeval (φ g) (p.map (algebraMap K L)) = 0 := by
    rw [aeval_map_algebraMap, aeval_algHom_apply, hp, map_zero]
  have hpL : p.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hp0
  have hcL : g.charpoly.map (algebraMap K L) ≠ 0 :=
    (g.charpoly_monic.map _).ne_zero
  rw [← Polynomial.map_dvd_map' (algebraMap K L)]
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots hcL ?_
  rw [Multiset.le_iff_subset (nodup_roots hsep.map)]
  intro r hr
  have hroot : IsRoot (φ g).charpoly r := by
    rw [hchar]
    exact (mem_roots'.mp hr).2
  have hspec : r ∈ spectrum L (φ g) := Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have himg := spectrum.subset_polynomial_aeval (φ g) (p.map (algebraMap K L)) ⟨r, hspec, rfl⟩
  rw [hzero] at himg
  have hev : eval r (p.map (algebraMap K L)) = 0 := by
    by_cases h : n = 0
    · subst h
      exact absurd (isUnit_of_subsingleton _) (spectrum.mem_iff.mp hspec)
    · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
      simpa using himg
  exact (mem_roots hpL).mpr hev
