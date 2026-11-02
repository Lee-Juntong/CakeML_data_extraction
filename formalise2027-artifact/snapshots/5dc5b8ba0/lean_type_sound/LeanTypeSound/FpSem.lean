/-
  Translation of fpSemScript.sml
  Definitions of the floating point operations used in CakeML.
-/
import LeanTypeSound.HOL4Prelude

open HOL4

/- HOL4:
Datatype:
  fp_cmp = FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal
End
-/
inductive fp_cmp where
  | FP_Less
  | FP_LessEqual
  | FP_Greater
  | FP_GreaterEqual
  | FP_Equal
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  fp_uop = FP_Abs | FP_Neg | FP_Sqrt
End
-/
inductive fp_uop where
  | FP_Abs
  | FP_Neg
  | FP_Sqrt
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  fp_bop = FP_Add | FP_Sub | FP_Mul | FP_Div
End
-/
inductive fp_bop where
  | FP_Add
  | FP_Sub
  | FP_Mul
  | FP_Div
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  fp_top = FP_Fma
End
-/
inductive fp_top where
  | FP_Fma
deriving Repr, BEq, Inhabited

/- HOL4:
Definition fp_cmp_def:
  fp_cmp cmp =
  case cmp of
  | Lt  => fp64_lessThan
  | Leq => fp64_lessEqual
  | Gt  => fp64_greaterThan
  | Geq => fp64_greaterEqual
End
-/
-- Note: fp_cmp_fn takes an opb (from Ast) so we forward-declare
-- The actual definition will use opb from Ast.lean
-- For now we define it taking a Nat encoding
def fp_cmp_fn (cmp : Nat) : word64 → word64 → Bool :=
  match cmp with
  | 0 => fp64_lessThan      -- Lt
  | 1 => fp64_greaterThan   -- Gt
  | 2 => fp64_lessEqual     -- Leq
  | _ => fp64_greaterEqual  -- Geq
