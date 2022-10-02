-- Typing

import Syntax

-- Ctx

structure Ctx where 
  knds : Name -> Option Knd
  typs : Name -> Option Typ

def Ctx.nil : Ctx where 
  knds := fun _ => none
  typs := fun _ => none

def Ctx.consKnd (x : Name) (κ : Knd) (Γ : Ctx) : Ctx where
  knds := fun y => if x == y then κ else Γ.knds y
  typs := Γ.typs

def Ctx.consTyp (x : Name) (α : Typ) (Γ : Ctx) : Ctx where
  knds := Γ.knds
  typs := fun y => if x == y then α else Γ.typs y

-- Kinding

def inferKnd (Γ : Ctx) (α : Typ) : Option Knd :=
  match α with 
  | Typ.bas basTyp => 
    match basTyp with 
    | BasTyp.unt => Knd.unt
  | Typ.var x => Γ.knds x
  | Typ.all x κ β => do
    let μ <- inferKnd (Ctx.consKnd x κ Γ) β
    return Knd.arr κ μ
  | Typ.arr .. => Knd.unt

def checkKnd (Γ : Ctx) (α : Typ) (κ : Knd) : Bool :=
  match inferKnd Γ α with 
  | some κ' => κ == κ' 
  | none => false

-- Typing

def subTyp (x : Name) (ξ : Typ) (α : Typ) : Typ :=
  match α with 
  | Typ.bas .. => α
  | Typ.var y => if x == y then ξ else α
  | Typ.arr β γ => Typ.arr (subTyp x ξ β) (subTyp x ξ γ)
  | Typ.all y κ β => if x == y then α else Typ.all y κ (subTyp x ξ β)   

def inferTyp (Γ : Ctx) (t : Trm) : Option Typ :=
  match t with 
  | Trm.bas t' => 
    match t' with 
    | BasTrm.unt => Typ.bas BasTyp.unt
  | Trm.var x => Γ.typs x
  | Trm.lam x α b => do
    let β <- inferTyp (Ctx.consTyp x α Γ) b
    return Typ.arr α β
  | Trm.all x κ b => do
    let β <- inferTyp (Ctx.consKnd x κ Γ) b
    return Typ.all x κ β 
  | Trm.app f a => do
    let φ <- inferTyp Γ f
    match φ with 
    | Typ.arr α β => do
      let α' <- inferTyp Γ a
      guard $ α == α'
      return β
    | _ => none
  | Trm.ins f α => do
    let φ <- inferTyp Γ f
    match φ with
    | Typ.all x κ β => do
      let κ' <- inferKnd Γ α
      guard $ κ == κ'
      return subTyp x α β
    | _ => none
  | Trm.loc x β b a => do
    let β' <- inferTyp Γ b 
    guard (β == β')
    inferTyp (Ctx.consTyp x β Γ) a

def checkTyp (Γ : Ctx) (t : Trm) (α : Typ) : Bool :=
  match inferTyp Γ t with 
  | some α' => α == α'
  | none => false

-- #eval 
--   inferTyp 
--     (Ctx.consTyp (Name.mk "x") (Typ.bas BasTyp.unt) Ctx.nil)
--     (Trm.var (Name.mk "x")) 