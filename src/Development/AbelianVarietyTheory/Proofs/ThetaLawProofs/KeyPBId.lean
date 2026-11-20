import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem keyPB_id : ∀ (R : Type) [CommRing R] (x : KeyIn R), KeyPB x x (RingHom.id R) :=
  fun _ _ x => GlobalTheory.KeyPow.keyPB_refl x

end GlobalTheory
