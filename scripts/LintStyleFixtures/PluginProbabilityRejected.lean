/-! Active retired notation must be rejected even when a local macro hides its semantics. -/
syntax "$ᵖ" term : term
macro_rules | `($ᵖ $x) => `($x)
syntax "Pr_{" term "}" : term
macro_rules | `(Pr_{ $x }) => `($x)
syntax "Pr[" term "]" : term
macro_rules | `(Pr[ $x ]) => `($x)
syntax "𝒮[" term "]" : term
macro_rules | `(𝒮[ $x ]) => `($x)

def legacySample := $ᵖ (1 : Nat)
def legacyPmfEvent := Pr_{ (1 : Nat) }
def legacyScalar := Pr[ (1 : Nat) ]
#guard_msgs (drop error) in
def legacySupport := 𝒮[ (1 : Nat) ]
