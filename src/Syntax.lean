-- Syntax

-- Name

structure Name where
  label : String
  deriving BEq, Repr

-- Knd: Kind

inductive Knd where
| unt : Knd
| arr : Knd -> Knd -> Knd
deriving BEq, Repr

-- Typ: Type

inductive BasTyp where
| unt : BasTyp
deriving BEq, Repr

inductive Typ where 
| bas : BasTyp -> Typ
| var : Name -> Typ
| all : Name -> Knd -> Typ -> Typ
| arr : Typ -> Typ -> Typ
deriving BEq, Repr

-- Trm: Term

inductive BasTrm where
| unt : BasTrm
deriving BEq, Repr

inductive Trm where
| bas : BasTrm -> Trm
| var : Name -> Trm
| lam : Name -> Typ -> Trm -> Trm
| all : Name -> Knd -> Trm -> Trm
| app : Trm -> Trm -> Trm
| ins : Trm -> Typ -> Trm
| loc : Name -> Typ -> Trm -> Trm -> Trm
deriving BEq, Repr


-- Dec: Declaration

-- constructor
inductive Con where
deriving BEq, Repr

-- destructor
inductive Des where
deriving BEq, Repr

inductive Dec where
-- term def
| trm : Name -> Typ -> Trm -> Dec
-- data def
| dat : Name -> Knd -> List Con -> Dec
-- codata def
| cod : Name -> Knd -> List Des -> Dec
deriving BEq, Repr
