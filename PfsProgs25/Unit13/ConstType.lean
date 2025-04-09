import Lean

open Lean Meta Elab Term Tactic

def getTypeM (name : Name) : MetaM <| Option Format := do
  let env ← getEnv
  env.find? name |>.mapM
    (fun d => ppExpr d.type)

def getTypeCore (name : Name) : CoreM <| Option Format :=
  getTypeM name |>.run'

#eval getTypeM ``Nat.succ_le_succ

def getProofM (name : Name) : MetaM <| Option Format := do
  let env ← getEnv
  match env.find? name with
  | none => return none
  | some info =>
    match info.value? with
    | some t => ppExpr t
    | none => return none

#eval getProofM ``Nat.succ_le_succ
#eval getTypeM ``Nat.rec
#eval getProofM ``Nat.rec


/-
inductive Lean.ConstantInfo : Type
number of parameters: 0
constructors:
Lean.ConstantInfo.axiomInfo : AxiomVal → ConstantInfo
Lean.ConstantInfo.defnInfo : DefinitionVal → ConstantInfo
Lean.ConstantInfo.thmInfo : TheoremVal → ConstantInfo
Lean.ConstantInfo.opaqueInfo : OpaqueVal → ConstantInfo
Lean.ConstantInfo.quotInfo : QuotVal → ConstantInfo
Lean.ConstantInfo.inductInfo : InductiveVal → ConstantInfo
Lean.ConstantInfo.ctorInfo : ConstructorVal → ConstantInfo
Lean.ConstantInfo.recInfo : RecursorVal → ConstantInfo
-/
#print ConstantInfo
