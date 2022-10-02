-- Syntax

-- Name

structure Name where
  label : String
deriving BEq, Repr

instance : ToString Name where 
  toString name := name.label

-- Knd: Kind

inductive Knd where
  | unt : Knd
  | arr : Knd -> Knd -> Knd
deriving BEq, Repr

instance : ToString Knd where
  toString := toString ∘ repr

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

instance : ToString Typ where
  toString := toString ∘ repr

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

instance : ToString Trm where
  toString := toString ∘ repr

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

instance : ToString Dec where
  toString := toString ∘ repr
