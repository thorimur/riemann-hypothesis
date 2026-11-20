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

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

noncomputable def UpperTheory.Reformulated.B.NormalizedMatrixSpan.Normd :
    {C : Type} →
      [inst : Field C] →
        {N : ℕ} → {Γ : Type} → [inst_1 : Group Γ] → (Γ →* GL (Fin N) C) → Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N) → Prop :=
    fun {C : Type} [Field C] {N : ℕ} {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C)
        (A : Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N)) ↦
      ∀ (g : Γ),
        ∀ a ∈ A,
          (↑((ρ : Γ → GL (Fin N) C) g) : Matrix (Fin N) (Fin N) C) * a *
              (↑((ρ : Γ → GL (Fin N) C) g⁻¹) : Matrix (Fin N) (Fin N) C) ∈
            A

noncomputable def UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens :
    {Γ C : Type} →
      [inst : Group Γ] →
        [inst_1 : Field C] →
          {N : ℕ} → (Γ →* GL (Fin N) C) → Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N) → Set (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N) :=
    fun {Γ C : Type} [Group Γ] [Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N)) ↦
      {x : UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N | ∃ a ∈ A, ∃ (g : Γ), x = a * (↑((ρ : Γ → GL (Fin N) C) g) : Matrix (Fin N) (Fin N) C)}

theorem UpperTheory.Reformulated.B.NormalizedMatrixSpan.span_mul :
    ∀ {Γ C : Type} [inst : Group Γ] [inst_1 : Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C)
      (A : Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N)),
      UpperTheory.Reformulated.B.NormalizedMatrixSpan.Normd ρ A →
        ∀ (x y : UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N),
          x ∈ Submodule.span C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens ρ A) →
            y ∈ Submodule.span C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens ρ A) → x * y ∈ Submodule.span C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens ρ A) := by
  intro Γ C _ _ N ρ A hA x y hx hy
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, ha, g, rfl⟩, _, ⟨b, hb, k, rfl⟩, rfl⟩
  refine ⟨a * ((ρ g : Matrix (Fin N) (Fin N) C) * b * (ρ g⁻¹ : Matrix (Fin N) (Fin N) C)),
    A.mul_mem ha (hA g b hb), g * k, ?_⟩
  have e : (ρ g⁻¹ : Matrix (Fin N) (Fin N) C) * (ρ (g * k) : Matrix (Fin N) (Fin N) C)
      = (ρ k : Matrix (Fin N) (Fin N) C) := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel_left]
  simp only [mul_assoc, e]
