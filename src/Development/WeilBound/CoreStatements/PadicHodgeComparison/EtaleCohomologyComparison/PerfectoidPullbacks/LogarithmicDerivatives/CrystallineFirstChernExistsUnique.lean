import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassReductionCompatible

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb

theorem clift_ex : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X),
    (∀ T, ∃ p : Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y, p ≫ D.f = B.thPt (G.obj T)) → Nonempty (B.CLift G D) := @GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift

theorem firstChern_acris_family_exists : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (D : E.LineData M.X),
    sSup (𝒱D D) = ⊤ → ∃ x : (M.HS false 2).lim, B.IsFirstChernFamily M.p D (okToOC l K) false x.1 := @GlobalTheory.CompanionTheory.FirstChernClassFactorial.exists_C1H

end CrystallineSemistableComparison.Pb
