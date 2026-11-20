import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem GenFib.nonempty_of_baseChange :
    Out.PolBaseChangeSt → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))), Nonempty (GenFib P) := by
  intro hB K _ _ P
  obtain ⟨P₀, φ, h⟩ := exists_isPolFibre hB (algebraMap (𝓞 K) K) P
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis P₀.A P₀.smoothDim
  exact ⟨⟨P₀, φ, h, v, hv⟩⟩

end GlobalTheory.CM
