-- Auto-generated LEAN 4 file from HOL4 translation
-- Theory: ast
-- Generated using Gemini API

-- Import ancestor theories
import CML_Lean.namespace
import CML_Lean.location

namespace CML_Lean.ast

/-
Original HOL4 Datatype: lit
lit =
    IntLit int
  | Char char
  | StrLit string
  | Word8 word8
  | Word64 word64
  | Float64 word64
-/
inductive Lit where
  | IntLit  : Int → Lit
  | Char    : Char → Lit
  | StrLit  : String → Lit
  | Word8   : UInt8 → Lit
  | Word64  : UInt64 → Lit
  | Float64 : UInt64 → Lit -- Raw bit representation of a float
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: opn
opn = Plus | Minus | Times | Divide | Modulo
-/
inductive Opn where
  | Plus   : Opn
  | Minus  : Opn
  | Times  : Opn
  | Divide : Opn
  | Modulo : Opn
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: opb
opb = Lt | Gt | Leq | Geq
-/
inductive Opb where
  | Lt  : Opb
  | Gt  : Opb
  | Leq : Opb
  | Geq : Opb
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: opw
opw = Andw | Orw | Xor | Add | Sub
-/
inductive Opw where
  | Andw : Opw
  | Orw  : Opw
  | Xor  : Opw
  | Add  : Opw
  | Sub  : Opw
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: shift
shift = Lsl | Lsr | Asr | Ror
-/
inductive Shift where
  | Lsl : Shift
  | Lsr : Shift
  | Asr : Shift
  | Ror : Shift
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: fp_cmp
fp_cmp = FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal
-/
inductive FpCmp where
  | FP_Less       : FpCmp
  | FP_LessEqual  : FpCmp
  | FP_Greater    : FpCmp
  | FP_GreaterEqual : FpCmp
  | FP_Equal      : FpCmp
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: fp_uop
fp_uop = FP_Abs | FP_Neg | FP_Sqrt
-/
inductive FpUop where
  | FP_Abs  : FpUop
  | FP_Neg  : FpUop
  | FP_Sqrt : FpUop
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: fp_bop
fp_bop = FP_Add | FP_Sub | FP_Mul | FP_Div
-/
inductive FpBop where
  | FP_Add : FpBop
  | FP_Sub : FpBop
  | FP_Mul : FpBop
  | FP_Div : FpBop
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: fp_top
fp_top = FP_Fma
-/
inductive FpTop where
  | FP_Fma : FpTop
  deriving Repr, DecidableEq

/-
Original HOL4 Type: modN
“:string”

(* Variable names *)
Type varN = “:string”

(* Constructor names (from datatype definitions) *)
Type conN = ``: string``
-/
abbrev ModN := String

/-
Original HOL4 Type: typeN
``: string``
-/
abbrev TypeN := String

/-
Original HOL4 Type: tvarN
``: string``
-/
abbrev TvarN := String

/-
Original HOL4 Datatype: word_size
word_size = W8 | W64
-/
inductive WordSize where
  | W8  : WordSize
  | W64 : WordSize
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: thunk_mode
thunk_mode = Evaluated | NotEvaluated
-/
inductive ThunkMode where
  | Evaluated    : ThunkMode
  | NotEvaluated : ThunkMode
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: thunk_op
thunk_op =
    AllocThunk thunk_mode
  | UpdateThunk thunk_mode
  | ForceThunk
-/
inductive ThunkOp where
  | AllocThunk  : ThunkMode → ThunkOp
  | UpdateThunk : ThunkMode → ThunkOp
  | ForceThunk  : ThunkOp
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: op
op =
  (* Operations on integers *)
    Opn opn
  | Opb opb
  (* Operations on words *)
  | Opw word_size opw
  | Shift word_size shift num
  | Equality
  (* FP operations *)
  | FP_cmp fp_cmp
  | FP_uop fp_uop
  | FP_bop fp_bop
  | FP_top fp_top
  (* Floating-point <-> word translations *)
  | FpFromWord
  | FpToWord
  (* Function application *)
  | Opapp
  (* Reference operations *)
  | Opassign
  | Opref
  | Opderef
  (* Word8Array operations *)
  | Aw8alloc
  | Aw8sub
  | Aw8length
  | Aw8update
  (* Word/integer conversions *)
  | WordFromInt word_size
  | WordToInt word_size
  (* string/bytearray conversions *)
  | CopyStrStr
  | CopyStrAw8
  | CopyAw8Str
  | CopyAw8Aw8
  | XorAw8Str_unsafe
  (* Char operations *)
  | Ord
  | Chr
  | Chopb opb
  (* String operations *)
  | Implode
  | Explode
  | Strsub
  | Strlen
  | Strcat
  (* Vector operations *)
  | VfromList
  | Vsub
  | Vlength
  (* Array operations *)
  | Aalloc
  | AallocEmpty
  | AallocFixed
  | Asub
  | Alength
  | Aupdate
  (* Unsafe array accesses *)
  | Asub_unsafe
  | Aupdate_unsafe
  | Aw8sub_unsafe
  | Aw8update_unsafe
  (* thunk operations *)
  | ThunkOp thunk_op
  (* List operations *)
  | ListAppend
  (* Configure the GC *)
  | ConfigGC
  (* Call a given foreign function *)
  | FFI string
  (* Evaluate new code in a given env *)
  | Eval
  (* Get the identifier of an env object *)
  | Env_id
-/
inductive Op where
  -- Operations on integers
  | Opn             : Opn → Op
  | Opb             : Opb → Op
  -- Operations on words
  | Opw             : WordSize → Opw → Op
  | Shift           : WordSize → Shift → Nat → Op
  | Equality        : Op
  -- FP operations
  | FpCmp           : FpCmp → Op
  | FpUop           : FpUop → Op
  | FpBop           : FpBop → Op
  | FpTop           : FpTop → Op
  -- Floating-point <-> word translations
  | FpFromWord      : Op
  | FpToWord        : Op
  -- Function application
  | Opapp           : Op
  -- Reference operations
  | Opassign        : Op
  | Opref           : Op
  | Opderef         : Op
  -- Word8Array operations
  | Aw8alloc        : Op
  | Aw8sub          : Op
  | Aw8length       : Op
  | Aw8update       : Op
  -- Word/integer conversions
  | WordFromInt     : WordSize → Op
  | WordToInt       : WordSize → Op
  -- string/bytearray conversions
  | CopyStrStr      : Op
  | CopyStrAw8      : Op
  | CopyAw8Str      : Op
  | CopyAw8Aw8      : Op
  | XorAw8Str_unsafe : Op
  -- Char operations
  | Ord             : Op
  | Chr             : Op
  | Chopb           : Opb → Op
  -- String operations
  | Implode         : Op
  | Explode         : Op
  | Strsub          : Op
  | Strlen          : Op
  | Strcat          : Op
  -- Vector operations
  | VfromList       : Op
  | Vsub            : Op
  | Vlength         : Op
  -- Array operations
  | Aalloc          : Op
  | AallocEmpty     : Op
  | AallocFixed     : Op
  | Asub            : Op
  | Alength         : Op
  | Aupdate         : Op
  -- Unsafe array accesses
  | Asub_unsafe     : Op
  | Aupdate_unsafe  : Op
  | Aw8sub_unsafe   : Op
  | Aw8update_unsafe : Op
  -- thunk operations
  | ThunkOp         : ThunkOp → Op
  -- List operations
  | ListAppend      : Op
  -- Configure the GC
  | ConfigGC        : Op
  -- Call a given foreign function
  | FFI             : String → Op
  -- Evaluate new code in a given env
  | Eval            : Op
  -- Get the identifier of an env object
  | Env_id          : Op
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: op_class
op_class =
    EvalOp (* Eval primitive *)
  | FunApp (* function application *)
  | Force (* forcing a thunk *)
  | Simple (* arithmetic operation, no finite-precision/reals *)
-/
inductive OpClass where
  | EvalOp : OpClass
  | FunApp : OpClass
  | Force  : OpClass
  | Simple : OpClass
  deriving Repr, DecidableEq

/-
Original HOL4 Definition: getOpClass_def
getOpClass op =
 case op of
  | Opapp => FunApp
  | Eval => EvalOp
  | ThunkOp t => (if t = ForceThunk then Force else Simple)
  | _ => Simple
-/
def get_op_class (op_val : Op) : OpClass := 
  match op_val with
  | Op.Opapp             => OpClass.FunApp
  | Op.Eval              => OpClass.EvalOp
  | Op.ThunkOp (ThunkOp.ForceThunk) => OpClass.Force
  | Op.ThunkOp _         => OpClass.Simple
  | _                    => OpClass.Simple

/-
Original HOL4 Definition: isFpBool_def
isFpBool op = case op of FP_cmp _ => T | _ => F
-/
def is_fp_bool (op_val : Op) : Bool := 
  match op_val with
  | Op.FpCmp _ => true
  | _          => false

/-
Original HOL4 Datatype: lop
lop = And | Or
-/
inductive Lop where
  | And : Lop
  | Or  : Lop
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: ast_t
ast_t =
  (* Type variables that the user writes down ('a, 'b, etc.) *)
    Atvar tvarN
  (* Function type *)
  | Atfun ast_t ast_t
  (* Tuple type *)
  | Attup (ast_t list)
  (* Type constructor applications.
    0-ary type applications represent unparameterised types (e.g., num or string) *)
  | Atapp (ast_t list) ((modN, typeN) id)
-/
inductive AstT where
  -- Type variables that the user writes down ('a, 'b, etc.)
  | Atvar : TvarN → AstT
  -- Function type
  | Atfun : AstT → AstT → AstT
  -- Tuple type
  | Attup : List AstT → AstT
  -- Type constructor applications.
  -- 0-ary type applications represent unparameterised types (e.g., num or string)
  | Atapp : List AstT → cml_id TypeN ModN → AstT
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: pat
pat =
    Pany
  | Pvar varN
  | Plit lit
  (* Constructor applications.
     A Nothing constructor indicates a tuple pattern. *)
  | Pcon (((modN, conN) id) option) (pat list)
  | Pref pat
  (* Pattern alias. *)
  | Pas pat varN
  | Ptannot pat ast_t
-/
inductive Pat where
  | Pany     : Pat
  | Pvar     : VarN → Pat
  | Plit     : Lit → Pat
  -- Constructor applications.
  -- A none constructor indicates a tuple pattern.
  | Pcon     : Option (cml_id ConN ModN) → List Pat → Pat
  | Pref     : Pat → Pat
  -- Pattern alias.
  | Pas      : Pat → VarN → Pat
  | Ptannot  : Pat → AstT → Pat
  deriving Repr, DecidableEq

/-
Original HOL4 Datatype: exp
exp =
    Raise exp
  | Handle exp ((pat # exp) list)
  | Lit lit
  (* Constructor application.
     A Nothing constructor indicates a tuple pattern. *)
  | Con (((modN, conN)id)option) (exp list)
  | Var ((modN, varN) id)
  | Fun varN exp
  (* Application a primitive operator to arguments.
     Includes function application. *)
  | App op (exp list)
  (* Logical operations (and, or) *)
  | Log lop exp exp
  | If exp exp exp
  (* Pattern matching *)
  | Mat exp ((pat # exp) list)
  (* A let expression
     A Nothing value for the binding indicates that this is a
     sequencing expression, that is: (e1; e2). *)
  | Let (varN option) exp exp
  (* Local definition (potentially) mutually recursive
     functions.
     The first varN is the function's name, and the second varN
     is its parameter. *)
  | Letrec ((varN # varN # exp) list) exp
  | Tannot exp ast_t
  (* Location annotated expressions, not expected in source programs *)
  | Lannot exp locs
-/
inductive Exp where
  | Raise    : Exp → Exp
  | Handle   : Exp → List (Pat × Exp) → Exp
  | Lit      : Lit → Exp
  -- Constructor application.
  -- A none constructor indicates a tuple pattern.
  | Con      : Option (cml_id ConN ModN) → List Exp → Exp
  | Var      : cml_id VarN ModN → Exp
  | Fun      : VarN → Exp → Exp
  -- Application a primitive operator to arguments.
  -- Includes function application.
  | App      : Op → List Exp → Exp
  -- Logical operations (and, or)
  | Log      : Lop → Exp → Exp → Exp
  | If       : Exp → Exp → Exp → Exp
  -- Pattern matching
  | Mat      : Exp → List (Pat × Exp) → Exp
  -- A let expression
  -- A none value for the binding indicates that this is a
  -- sequencing expression, that is: (e1; e2).
  | Let      : Option VarN → Exp → Exp → Exp
  -- Local definition (potentially) mutually recursive
  -- functions.
  -- The first VarN is the function's name, and the second VarN
  -- is its parameter.
  | Letrec   : List (VarN × VarN × Exp) → Exp → Exp
  | Tannot   : Exp → AstT → Exp
  -- Location annotated expressions, not expected in source programs
  | Lannot   : Exp → Locs → Exp
  deriving Repr, DecidableEq

/-
Original HOL4 Type: type_def
``: ( tvarN list # typeN # (conN # ast_t list) list) list``
-/
abbrev TypeDef := List (List TvarN × TypeN × List (ConN × List AstT))

/-
Original HOL4 Datatype: dec
dec =
  (* Top-level bindings
   * The pattern allows several names to be bound at once *)
    Dlet locs pat exp
  (* Mutually recursive function definition *)
  | Dletrec locs ((varN # varN # exp) list)
  (* Type definition
     Defines several data types, each which has several
     named variants, which can in turn have several arguments.
   *)
  | Dtype locs type_def
  (* Type abbreviations *)
  | Dtabbrev locs (tvarN list) typeN ast_t
  (* New exceptions *)
  | Dexn locs conN (ast_t list)
  (* Module *)
  | Dmod modN (dec list)
  (* Local: local part, visible part *)
  | Dlocal (dec list) (dec list)
  (* Store current lexical env in an env value *)
  | Denv tvarN
-/
inductive Dec where
  -- Top-level bindings
  -- The pattern allows several names to be bound at once
  | Dlet      : Locs → Pat → Exp → Dec
  -- Mutually recursive function definition
  | Dletrec   : Locs → List (VarN × VarN × Exp) → Dec
  -- Type definition
  -- Defines several data types, each which has several
  -- named variants, which can in turn have several arguments.
  | Dtype     : Locs → TypeDef → Dec
  -- Type abbreviations
  | Dtabbrev  : Locs → List TvarN → TypeN → AstT → Dec
  -- New exceptions
  | Dexn      : Locs → ConN → List AstT → Dec
  -- Module
  | Dmod      : ModN → List Dec → Dec
  -- Local: local part, visible part
  | Dlocal    : List Dec → List Dec → Dec
  -- Store current lexical env in an env value
  | Denv      : TvarN → Dec
  deriving Repr, DecidableEq

/-
Original HOL4 Definition: pat_bindings_def
pat_bindings Pany already_bound = already_bound ∧
  pat_bindings (Pvar n) already_bound = n::already_bound ∧
  pat_bindings (Plit l) already_bound = already_bound ∧
  pat_bindings (Pcon v0 ps) already_bound = pats_bindings ps already_bound ∧
  pat_bindings (Pref p) already_bound = pat_bindings p already_bound ∧
  pat_bindings (Pas p i) already_bound = pat_bindings p (i::already_bound) ∧
  pat_bindings (Ptannot p v1) already_bound = pat_bindings p already_bound ∧
  pats_bindings [] already_bound = already_bound ∧
  pats_bindings (p::ps) already_bound =
  pats_bindings ps (pat_bindings p already_bound)
-/
def pat_bindings (p : Pat) (already_bound : List VarN) : List VarN :=
  let rec pats_bindings (ps : List Pat) (acc : List VarN) : List VarN := 
    match ps with
    | []      => acc
    | p' :: ps' => pats_bindings ps' (pat_bindings p' acc)
  match p with
  | Pat.Pany             => already_bound
  | Pat.Pvar n           => n :: already_bound
  | Pat.Plit _           => already_bound
  | Pat.Pcon _ ps_list   => pats_bindings ps_list already_bound
  | Pat.Pref p'          => pat_bindings p' already_bound
  | Pat.Pas p' i         => pat_bindings p' (i :: already_bound)
  | Pat.Ptannot p' _     => pat_bindings p' already_bound

/-
Original HOL4 Definition: every_exp_def
(every_exp p (Raise e) ⇔
             p (Raise e) ∧ every_exp p e) ∧
  (every_exp p (Handle e pes) ⇔
             p (Handle e pes) ∧ every_exp p e ∧ EVERY (λ(pat,e). every_exp p e) pes) ∧
  (every_exp p (ast$Lit l) ⇔
             p (ast$Lit l)) ∧
  (every_exp p (Con cn es) ⇔
             p (Con cn es) ∧ EVERY (every_exp p) es) ∧
  (every_exp p (Var v) ⇔
             p (Var v)) ∧
  (every_exp p (Fun x e) ⇔
             p (Fun x e) ∧ every_exp p e) ∧
  (every_exp p (App op es) ⇔
             p (App op es) ∧ EVERY (every_exp p) es) ∧
  (every_exp p (Log lop e1 e2) ⇔
             p (Log lop e1 e2) ∧ every_exp p e1 ∧ every_exp p e2) ∧
  (every_exp p (If e1 e2 e3) ⇔
             p (If e1 e2 e3) ∧ every_exp p e1 ∧ every_exp p e2 ∧ every_exp p e3) ∧
  (every_exp p (Mat e pes) ⇔
             p (Mat e pes) ∧ every_exp p e ∧ EVERY (λ(pat,e). every_exp p e) pes) ∧
  (every_exp p (Let x e1 e2) ⇔
             p (Let x e1 e2) ∧ every_exp p e1 ∧ every_exp p e2) ∧
  (every_exp p (Tannot e a) ⇔
             p (Tannot e a) ∧ every_exp p e) ∧
  (every_exp p (Lannot e a) ⇔
             p (Lannot e a) ∧ every_exp p e) ∧
  (every_exp p (Letrec funs e) ⇔
             p (Letrec funs e) ∧ every_exp p e ∧ EVERY (λ(n,v,e). every_exp p e) funs)
-/
def every_exp (p : Exp → Prop) (e : Exp) : Prop :=
  match e with
  | Exp.Raise e'           => p (Exp.Raise e') ∧ every_exp p e'
  | Exp.Handle e' pes      => p (Exp.Handle e' pes) ∧ every_exp p e' ∧ (List.Forall (fun (_, exp_val) => every_exp p exp_val) pes)
  | Exp.Lit _              => p (Exp.Lit e.lit)
  | Exp.Con _ es           => p (Exp.Con e.con es) ∧ (List.Forall (every_exp p) es)
  | Exp.Var _              => p (Exp.Var e.var)
  | Exp.Fun _ e'           => p (Exp.Fun e.fun e') ∧ every_exp p e'
  | Exp.App _ es           => p (Exp.App e.op es) ∧ (List.Forall (every_exp p) es)
  | Exp.Log _ e1 e2        => p (Exp.Log e.lop e1 e2) ∧ every_exp p e1 ∧ every_exp p e2
  | Exp.If e1 e2 e3        => p (Exp.If e1 e2 e3) ∧ every_exp p e1 ∧ every_exp p e2 ∧ every_exp p e3
  | Exp.Mat e' pes         => p (Exp.Mat e' pes) ∧ every_exp p e' ∧ (List.Forall (fun (_, exp_val) => every_exp p exp_val) pes)
  | Exp.Let _ e1 e2        => p (Exp.Let e.optionVarN e1 e2) ∧ every_exp p e1 ∧ every_exp p e2
  | Exp.Tannot e' _        => p (Exp.Tannot e' e.astT) ∧ every_exp p e'
  | Exp.Lannot e' _        => p (Exp.Lannot e' e.locs) ∧ every_exp p e'
  | Exp.Letrec funs e'     => p (Exp.Letrec funs e') ∧ every_exp p e' ∧ (List.Forall (fun (_, _, exp_val) => every_exp p exp_val) funs)

/-
Original HOL4 Definition: Seqs_def
Seqs [] = Con NONE [] ∧
  Seqs (x::xs) = Let NONE x (Seqs xs)
-/
def Seqs (es : List Exp) : Exp :=
  match es with
  | []      => Exp.Con none []
  | x :: xs => Exp.Let none x (Seqs xs)

/-
Original HOL4 Definition: Apps_def
Apps f [] = f ∧
  Apps f (x::xs) = Apps (App Opapp [f; x]) xs
-/
def Apps (f : Exp) (args : List Exp) : Exp :=
  match args with
  | []      => f
  | x :: xs => Apps (Exp.App Op.Opapp [f, x]) xs

/-
Original HOL4 Definition: Funs_def
Funs [] e = e ∧
  Funs (x::xs) e = Fun x (Funs xs e)
-/
def Funs (vars : List VarN) (e : Exp) : Exp :=
  match vars with
  | []      => e
  | x :: xs => Exp.Fun x (Funs xs e)

end CML_Lean.ast
