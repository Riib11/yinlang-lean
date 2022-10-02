-- # Typing

import Syntax

-- ## TypingM

abbrev TypingM α := Except String α

def assert : Bool -> String -> TypingM Unit
  | true => fun _ => return default
  | false => throw

def void (m : TypingM α) : TypingM Unit := do
  let _ <- m
  return default

-- ## Ctx

structure Ctx where 
  knds : Name -> TypingM Knd
  typs : Name -> TypingM Typ

def Ctx.nil : Ctx where 
  knds := fun x => throw s!"The type var {x} isn't in context."
  typs := fun x => throw s!"The term var {x} isn't in context."

def Ctx.consKnd (x : Name) (κ : Knd) (Γ : Ctx) : Ctx where
  knds := fun y => if x == y then return κ else Γ.knds y
  typs := Γ.typs

def Ctx.consTyp (x : Name) (α : Typ) (Γ : Ctx) : Ctx where
  knds := Γ.knds
  typs := fun y => if x == y then return α else Γ.typs y

-- ## Kinding

def Knd.uni : Knd -> Knd -> TypingM Unit
  | κ, κ' => assert (κ == κ') s!"The kinds {κ} and {κ'} don't unify."

notation κ " ~~ " κ' => void (Knd.uni κ κ')

def Knd.infer (Γ : Ctx) : Typ -> TypingM Knd
  | Typ.bas BasTyp.unt => return Knd.unt
  | Typ.var x => Γ.knds x
  | Typ.all x κ β => do
    let μ <- Knd.infer (Ctx.consKnd x κ Γ) β
    return Knd.arr κ μ
  | Typ.arr .. => return Knd.unt

def Knd.chk (Γ : Ctx) (α : Typ) (κ : Knd) : TypingM Unit := do
  let κ' <- Knd.infer Γ α
  κ ~~ κ'

-- ## Typing

-- type variable substitution in a type
def Typ.sub (x : Name) (ξ : Typ) : Typ -> Typ
  | Typ.bas α => Typ.bas α
  | Typ.var y => 
    if x == y 
      then ξ 
      else Typ.var y
  | Typ.arr β γ => Typ.arr (Typ.sub x ξ β) (Typ.sub x ξ γ)
  | Typ.all y κ β => 
    if x == y 
      then Typ.all y κ β
      else Typ.all y κ (Typ.sub x ξ β)

def Typ.subTrm (x : Name) (ξ : Typ) : Trm -> Trm
  | Trm.bas t => Trm.bas t
  | Trm.var y => Trm.var y
  | Trm.lam y α b => Trm.lam y (Typ.sub x ξ α) (Typ.subTrm x ξ b)
  | Trm.all y κ b =>
    if x == y
      then Trm.all y κ b
      else Trm.all y κ (Typ.subTrm x ξ b)
  | Trm.app f a => Trm.app (Typ.subTrm x ξ f) (Typ.subTrm x ξ a)
  | Trm.ins f α => Trm.ins (Typ.subTrm x ξ f) (Typ.sub x ξ α)
  | Trm.loc y α a b => Trm.loc y (Typ.sub x ξ α) (Typ.subTrm x ξ a) (Typ.subTrm x ξ b)  

-- type-equality up to alpha-renaming
def Typ.uni : Typ -> Typ -> TypingM Typ
  | Typ.bas α, Typ.bas α' => do
    assert (α == α') s!"The types {Typ.bas α} and {Typ.bas α'} don't unify."
    return Typ.bas α
  | Typ.var x , Typ.var x' => do
    assert (x == x') s!"The types {Typ.var x} and {Typ.var x'} don't unify."
    return Typ.var x
  | Typ.arr β γ , Typ.arr β' γ' => do
    let β'' <- Typ.uni β β'
    let γ'' <- Typ.uni γ γ'
    return Typ.arr β'' γ''
  | Typ.all x κ β , Typ.all x' κ' β' => do
    assert (κ == κ') s!"The types {Typ.all x κ β} and {Typ.all x' κ' β'} don't unify."
    let β'' <- 
      (if x == x' 
        then Typ.uni β β'
        else Typ.uni β (Typ.sub x' (Typ.var x) β'))
    return Typ.all x κ β''
  | α , α' => throw s!"The types {α} and {α'} don't unify." 

notation α " ~ " α' => void (Typ.uni α α')

-- type inference
def Typ.infer (Γ : Ctx) : Trm -> TypingM Typ
  | Trm.bas BasTrm.unt => return Typ.bas BasTyp.unt
  | Trm.var x => Γ.typs x
  | Trm.lam x α b => do
    let β <- Typ.infer (Ctx.consTyp x α Γ) b
    return Typ.arr α β
  | Trm.all x κ b => do
    let β <- Typ.infer (Ctx.consKnd x κ Γ) b
    return Typ.all x κ β 
  | Trm.app f a => do
    let φ <- Typ.infer Γ f
    match φ with 
    | Typ.arr α β => do
      let α' <- Typ.infer Γ a
      α ~ α'
      return β
    | _ => throw s!"The applicant {f} has the non-function type {φ}."
  | Trm.ins f α => do
    let φ <- Typ.infer Γ f
    match φ with
    | Typ.all x κ β => do
      let κ' <- Knd.infer Γ α
      κ ~~ κ'
      return Typ.sub x α β
    | _ => throw s!"The type-applicant {f} has the non-polymorphic type {φ}"
  | Trm.loc x β b a => do
    let β' <- Typ.infer Γ b 
    β ~ β'
    Typ.infer (Ctx.consTyp x β Γ) a

def Typ.chk (Γ : Ctx) (t : Trm) (α : Typ) : TypingM Unit := do
  let α' <- Typ.infer Γ t
  α ~ α'
  return default

-- #eval 
--   Typ.infer 
--     (Ctx.consTyp (Name.mk "x") (Typ.bas BasTyp.unt) Ctx.nil)
--     (Trm.var (Name.mk "x")) 

-- ## Checking Declarations

def Dec.chk (Γ : Ctx) : Dec -> TypingM Unit
  | Dec.trm _x α a => Typ.chk Γ a α
  | _ => throw "unimpl"

-- ## Checking Program

def Prg.chk (Γ : Ctx) : Prg -> TypingM Unit
  | [] => return default
  | (d :: ds) => do
    void $ Dec.chk Γ d
    match d with 
    | Dec.trm x α _a => Prg.chk (Ctx.consTyp x α Γ) ds
    | _ => throw "unimpl"