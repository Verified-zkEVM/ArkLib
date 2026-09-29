import VCVio.OracleComp.Constructions.SampleableType.Measure

namespace RetiredProbabilityTestFixtures.Clean

noncomputable def probability : ENNReal := Pr{x ←$ᵗ Bool}[x = true]

def inert : String := "PMF SPMF Pr_{...} $ᵖ"

end RetiredProbabilityTestFixtures.Clean
