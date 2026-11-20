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
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe48.DR :
    (R B : Type) → [inst : CommRing R] → [inst_1 : CommRing B] → [Algebra R B] → Type :=
    fun (R B : Type) [CommRing R] [CommRing B] [Algebra R B] ↦ ExteriorAlgebra B Ω[B⁄R]

noncomputable def UpperTheory.Reformulated.B.Qe48.omB :
    (k : Type) →
      [inst : Field k] →
        (K : Type) →
          [inst_1 : Field K] → [inst_2 : Algebra k K] → Subalgebra k K → ℕ → Submodule k (UpperTheory.Reformulated.B.Qe48.DR k K) :=
    fun (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ) ↦
      Submodule.span k
        {y : UpperTheory.Reformulated.B.Qe48.DR k K |
          ∃ b ∈ B,
            ∃ (v : Fin q → K),
              (∀ (j : Fin q), v j ∈ B) ∧
                y =
                  b •
                    (ExteriorAlgebra.ιMulti K q : (Fin q → Ω[K⁄k]) → ExteriorAlgebra K Ω[K⁄k]) fun (j : Fin q) ↦
                      (KaehlerDifferential.D k K : K → Ω[K⁄k]) (v j)}

theorem UpperTheory.Reformulated.B.Qe48.om_mul :
    ∀ {L : Type} [inst : Field L] [inst_1 : Algebra ℂ L] (B : Subalgebra ℂ L) {p q : ℕ} {u w : UpperTheory.Reformulated.B.Qe48.DR ℂ L},
      u ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B p → w ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B q → u * w ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B (p + q) := by
  intro L _ _ B p q u w hu hw
  unfold UpperTheory.Reformulated.B.Qe48.omB at hu hw ⊢
  have h := Submodule.mul_mem_mul hu hw
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨b, hb, v, hv, rfl⟩, _, ⟨c, hc, v', hv', rfl⟩, rfl⟩
  refine ⟨b * c, B.mul_mem hb hc, Fin.append v v', ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact hv i
    · rw [Fin.append_right]; exact hv' i
  · show _ * _ = _
    rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_mul_ιMulti]
    congr 2
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
