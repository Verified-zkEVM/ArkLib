import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

namespace RetiredProbabilityTestFixtures.Clean

noncomputable def probability : ENNReal := Pr{let x ←$ᵗ Bool}[x = true]

def inert : String := "PMF SPMF Pr_{...} $ᵖ"

end RetiredProbabilityTestFixtures.Clean
