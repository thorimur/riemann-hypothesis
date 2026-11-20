import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SabModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isPrincipal_dim {K : Type} [Field K] {t : SAB H (Sp K)} (_h : IsPrincipal t) :
    ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  letI := t.grp
  haveI hs : IsSemiAbelian t.G := t.semi
  haveI : Smooth t.G.hom := hs.smooth
  haveI : GeometricallyConnected t.G.hom := hs.geomConnected
  have hc := t.G.hom.isConnected_preimage_singleton (IsLocalRing.closedPoint K)
  have hu : t.G.hom ⁻¹' {IsLocalRing.closedPoint K} = Set.univ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  haveI : PreconnectedSpace t.G.left := ⟨by rw [← hu]; exact hc.isPreconnected⟩
  exact exists_dim_of_preconnected t.G.hom hc.nonempty.some

def pol {K : Type} [Field K] (t : SAB H (Sp K)) (h : IsPrincipal t) : Out.PolAV (Sp K) where
  A := t.G
  isAb := ⟨inferInstance, t.semi.smooth, h.1, t.semi.geomConnected⟩
  g := (isPrincipal_dim h).choose
  smoothDim := (isPrincipal_dim h).choose_spec
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := h.2.1
  ktriv := h.2.2

end GlobalTheory.CompanionTheory.Ar.SabModel
