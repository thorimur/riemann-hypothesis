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

theorem UpperTheory.dvd_exponent_of_pow_eq_laurent_monomial :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O] [IsLocalRing O] (c : ℕ) (v : (LaurentPolynomial O)ˣ), (v : LaurentPolynomial O) ^ q = LaurentPolynomial.T (c : ℤ) → q ∣ c := by
  intro q _ O _ _ c v hv
  classical
  let φ : LaurentPolynomial O →+* LaurentPolynomial (IsLocalRing.ResidueField O) :=
    AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O)
  have hT : ∀ n : ℤ, φ (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
    intro n
    show AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O) (AddMonoidAlgebra.single n 1) =
      AddMonoidAlgebra.single n 1
    rw [AddMonoidAlgebra.mapRingHom_single, map_one]
  have hw : (φ v) ^ q = LaurentPolynomial.T (c : ℤ) := by
    rw [← map_pow, hv, hT]
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow (φ v)
  have hpq : p ^ q = Polynomial.X ^ (c + q * n) := by
    apply Polynomial.toLaurent_injective
    rw [map_pow, hp, mul_pow, hw, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add,
      Polynomial.toLaurent_X_pow]
    congr 1
  have hdeg := congrArg Polynomial.natDegree hpq
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_pow] at hdeg
  have h1 : q ∣ q * n + c := ⟨p.natDegree, by rw [add_comm]; exact hdeg.symm⟩
  exact (Nat.dvd_add_right (dvd_mul_right q n)).mp h1
