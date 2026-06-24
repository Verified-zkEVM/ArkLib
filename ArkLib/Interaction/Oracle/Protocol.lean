/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Telescope

/-!
# Oracle Protocol Builder

This module bundles an `Interaction.Oracle.Spec` together with its public-role
and oracle-interface decorations. The bundle is an authoring convenience: the
executable object remains `Interaction.Oracle.Reduction`.
-/

namespace Interaction.Oracle
namespace Spec

universe v

/-- A decorated oracle protocol shape: an `Oracle.Spec` plus the role and oracle
interface decorations needed to execute it. -/
structure Protocol where
  /-- The underlying oracle-spec interaction tree. -/
  spec : Oracle.Spec
  /-- Interaction.TwoParty.Role decoration for public nodes of `spec`. -/
  roles : Spec.RoleDeco spec
  /-- Oracle-interface decoration for oracle nodes of `spec`. -/
  oracleDeco : Spec.OracleDeco spec

namespace Protocol

/-- Terminal decorated protocol. -/
def done : Protocol where
  spec := .done
  roles := ⟨⟩
  oracleDeco := ⟨⟩

/-- Public-message node with an explicit role. -/
def «public» (role : Interaction.TwoParty.Role) (X : Type) (rest : X → Protocol) : Protocol where
  spec := .public X (fun x => (rest x).spec)
  roles := ⟨role, fun x => (rest x).roles⟩
  oracleDeco := fun x => (rest x).oracleDeco

/-- Oracle-message node with an explicit oracle interface. -/
def oracleWith (X : Type) (oi : OracleInterface X) (rest : Protocol) : Protocol where
  spec := .oracle X (fun _ => rest.spec)
  roles := rest.roles
  oracleDeco := ⟨oi, rest.oracleDeco⟩

/-- Oracle-message node using typeclass synthesis for its oracle interface. -/
def oracle (X : Type) [OracleInterface X] (rest : Protocol) : Protocol :=
  oracleWith X (inferInstance : OracleInterface X) rest

/-- Dependent sequential composition of decorated protocols. -/
def append (p : Protocol) (q : PublicTranscript p.spec → Protocol) : Protocol where
  spec := p.spec.append fun pt => (q pt).spec
  roles := RoleDeco.append p.spec (fun pt => (q pt).spec)
    p.roles (fun pt => (q pt).roles)
  oracleDeco := OracleDeco.append p.spec (fun pt => (q pt).spec)
    p.oracleDeco (fun pt => (q pt).oracleDeco)

@[simp]
theorem done_spec : done.spec = .done := rfl

@[simp]
theorem done_roles : done.roles = ⟨⟩ := rfl

@[simp]
theorem done_oracleDeco : done.oracleDeco = ⟨⟩ := rfl

@[simp]
theorem public_spec (role : Interaction.TwoParty.Role) (X : Type) (rest : X → Protocol) :
    («public» role X rest).spec = .public X (fun x => (rest x).spec) := rfl

@[simp]
theorem public_roles (role : Interaction.TwoParty.Role) (X : Type) (rest : X → Protocol) :
    («public» role X rest).roles = ⟨role, fun x => (rest x).roles⟩ := rfl

@[simp]
theorem public_oracleDeco (role : Interaction.TwoParty.Role) (X : Type) (rest : X → Protocol) :
    («public» role X rest).oracleDeco = (fun x => (rest x).oracleDeco) := rfl

@[simp]
theorem oracleWith_spec (X : Type) (oi : OracleInterface X) (rest : Protocol) :
    (oracleWith X oi rest).spec = .oracle X (fun _ => rest.spec) := rfl

@[simp]
theorem oracleWith_roles (X : Type) (oi : OracleInterface X) (rest : Protocol) :
    (oracleWith X oi rest).roles = rest.roles := rfl

@[simp]
theorem oracleWith_oracleDeco (X : Type) (oi : OracleInterface X) (rest : Protocol) :
    (oracleWith X oi rest).oracleDeco = ⟨oi, rest.oracleDeco⟩ := rfl

@[simp]
theorem oracle_spec (X : Type) [OracleInterface X] (rest : Protocol) :
    (oracle X rest).spec = .oracle X (fun _ => rest.spec) := rfl

@[simp]
theorem oracle_roles (X : Type) [OracleInterface X] (rest : Protocol) :
    (oracle X rest).roles = rest.roles := rfl

@[simp]
theorem oracle_oracleDeco (X : Type) [OracleInterface X] (rest : Protocol) :
    (oracle X rest).oracleDeco =
      ⟨(inferInstance : OracleInterface X), rest.oracleDeco⟩ := rfl

@[simp]
theorem append_spec (p : Protocol) (q : PublicTranscript p.spec → Protocol) :
    (p.append q).spec = p.spec.append (fun pt => (q pt).spec) := rfl

@[simp]
theorem append_roles (p : Protocol) (q : PublicTranscript p.spec → Protocol) :
    (p.append q).roles =
      RoleDeco.append p.spec (fun pt => (q pt).spec)
        p.roles (fun pt => (q pt).roles) := rfl

@[simp]
theorem append_oracleDeco (p : Protocol) (q : PublicTranscript p.spec → Protocol) :
    (p.append q).oracleDeco =
      OracleDeco.append p.spec (fun pt => (q pt).spec)
        p.oracleDeco (fun pt => (q pt).oracleDeco) := rfl

/-! ## Protocol telescopes -/

/-- State-machine telescopes of decorated oracle protocols. -/
abbrev Telescope {St : Type v}
    (round : St → Protocol)
    (step : (s : St) → PublicTranscript (round s).spec → St) : St → Type v :=
  Spec.Telescope (fun s => (round s).spec) step

namespace Telescope

variable {St : Type v} {round : St → Protocol}
    {step : (s : St) → PublicTranscript (round s).spec → St}
    {s : St}

/-- Constructor wrapper for terminating a decorated protocol telescope. -/
abbrev done (s : St) : Telescope round step s :=
  Spec.Telescope.done (round := fun s => (round s).spec) (step := step) s

/-- Constructor wrapper for extending a decorated protocol telescope. -/
abbrev extend (s : St)
    (cont : (pt : PublicTranscript (round s).spec) → Telescope round step (step s pt)) :
    Telescope round step s :=
  Spec.Telescope.extend (round := fun s => (round s).spec) (step := step) s cont

/-- Flatten a decorated protocol telescope to one decorated protocol. -/
def toProtocol (t : Telescope round step s) : Protocol where
  spec := Spec.Telescope.toSpec t
  roles := Spec.Telescope.toRoleDeco (fun s => (round s).roles) t
  oracleDeco := Spec.Telescope.toOracleDeco (fun s => (round s).oracleDeco) t

@[simp]
theorem toProtocol_spec (t : Telescope round step s) :
    t.toProtocol.spec = Spec.Telescope.toSpec t := rfl

@[simp]
theorem toProtocol_roles (t : Telescope round step s) :
    t.toProtocol.roles =
      Spec.Telescope.toRoleDeco (fun s => (round s).roles) t := rfl

@[simp]
theorem toProtocol_oracleDeco (t : Telescope round step s) :
    t.toProtocol.oracleDeco =
      Spec.Telescope.toOracleDeco (fun s => (round s).oracleDeco) t := rfl

@[simp]
theorem toProtocol_done (s : St) :
    (done (round := round) (step := step) s).toProtocol = Protocol.done := rfl

@[simp]
theorem toProtocol_extend (s : St)
    (cont : (pt : PublicTranscript (round s).spec) → Telescope round step (step s pt)) :
    (extend s cont).toProtocol =
      (round s).append (fun pt => (cont pt).toProtocol) := rfl

end Telescope
end Protocol
end Spec
end Interaction.Oracle
