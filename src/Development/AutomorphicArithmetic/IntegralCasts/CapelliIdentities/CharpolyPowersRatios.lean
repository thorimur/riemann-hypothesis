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
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable def UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios :
    {κ ι : Type} → [inst : Field κ] → (ι → κˣ) → Prop :=
    fun {κ ι : Type} [Field κ] (α : ι → κˣ) ↦ ∀ (i j : ι), i ≠ j → ∀ (m : ℕ), (0 : ℕ) < m → α i ^ m ≠ α j ^ m

theorem UpperTheory.Reformulated.B.CharpolyPowersRatios.charpoly_pow :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ),
      M.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) (↑(a i) : K)) →
        UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios a →
          ∀ (d : ℕ),
            (0 : ℕ) < d →
              (M ^ d).charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) ((↑(a i) : K) ^ d)) := by
  intro K _ n M a hM hfree d _
  have hinj : Function.Injective (fun i => (a i : K)) := by
    intro i j hij
    by_contra hne
    exact hfree i j hne 1 one_pos (by simpa using Units.ext hij)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i : K) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ (fun i => (a i : K)) hinj v hv
  let b : Module.Basis (Fin n) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' v hli _
  have hpow : ∀ j, Matrix.toLin' (M ^ d) (v j) = ((a j : K) ^ d) • v j := by
    intro j
    rw [Matrix.toLin'_pow]
    exact (hv j).pow_apply d
  have hmat : LinearMap.toMatrix b b (Matrix.toLin' (M ^ d)) =
      Matrix.diagonal (fun i => (a i : K) ^ d) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb, hpow, map_smul, ← hb]
    simp only [Module.Basis.repr_self, Matrix.diagonal_apply, Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul, mul_one]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, hmat, Matrix.charpoly_diagonal]
