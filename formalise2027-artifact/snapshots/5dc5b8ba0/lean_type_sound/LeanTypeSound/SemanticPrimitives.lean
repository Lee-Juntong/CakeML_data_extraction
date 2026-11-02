/-
  Translation of semanticPrimitivesScript.sml
  Definitions of semantic primitives (values, operations, etc.)
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Misc
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.Ffi
import LeanTypeSound.FpSem
import LeanTypeSound.Mlstring

open HOL4

/- HOL4:
Datatype:
  stamp = TypeStamp conN num | ExnStamp num
End
-/
inductive stamp where
  | TypeStamp : conN → Nat → stamp
  | ExnStamp : Nat → stamp
deriving Repr, BEq, Inhabited

/- HOL4:
-- v and sem_env are mutually recursive
Datatype:
  sem_env = <| v : (modN, varN, 'v) namespace ; c : (modN, conN, (num # stamp)) namespace |>
End
Datatype:
  v = Litv lit | Conv (stamp option) (v list) | Closure (v sem_env) varN exp
    | Recclosure (v sem_env) ((varN # varN # exp) list) varN
    | Loc bool num | Vectorv (v list) | Env (v sem_env) (num # num)
End
-/
mutual
inductive v where
  | Litv : lit → v
  | Conv : Option stamp → List v → v
  | Closure : sem_env → varN → exp → v
  | Recclosure : sem_env → List (varN × varN × exp) → varN → v
  | Loc : Bool → Nat → v
  | Vectorv : List v → v
  | Env : sem_env → Nat × Nat → v

inductive sem_env where
  | mk : «namespace» modN varN v →
         «namespace» modN conN (Nat × stamp) → sem_env
end

instance : BEq v := ⟨fun _ _ => sorry⟩
instance : BEq sem_env := ⟨fun _ _ => sorry⟩
instance : Inhabited v := ⟨.Litv (.IntLit 0)⟩
instance : Inhabited sem_env := ⟨.mk (.Bind [] []) (.Bind [] [])⟩

namespace sem_env
def v_ (e : sem_env) : «namespace» modN varN v :=
  match e with | .mk v _ => v
def c (e : sem_env) : «namespace» modN conN (Nat × stamp) :=
  match e with | .mk _ c => c
end sem_env

def sem_env_v (e : sem_env) := e.v_
def sem_env_c (e : sem_env) := e.c

/- HOL4:
Type env_ctor = ``: (modN, conN, (num # stamp)) namespace``
-/
abbrev env_ctor := «namespace» modN conN (Nat × stamp)

/- HOL4:
Type env_val = ``: (modN, varN, v) namespace``
-/
abbrev env_val := «namespace» modN varN v

-- Exception stamps
/- HOL4:
Definition bind_stamp_def: bind_stamp = ExnStamp 0
End
-/
def bind_stamp : stamp := .ExnStamp 0
def chr_stamp : stamp := .ExnStamp 1
def div_stamp : stamp := .ExnStamp 2
def subscript_stamp : stamp := .ExnStamp 3

def bind_exn_v : v := .Conv (some bind_stamp) []
def chr_exn_v : v := .Conv (some chr_stamp) []
def div_exn_v : v := .Conv (some div_stamp) []
def sub_exn_v : v := .Conv (some subscript_stamp) []

def bool_type_num : Nat := 0
def list_type_num : Nat := 1

-- Result types
/- HOL4:
Datatype:
  abort = Rtype_error | Rtimeout_error | Rffi_error final_event
End
-/
inductive abort where
  | Rtype_error : abort
  | Rtimeout_error : abort
  | Rffi_error : final_event → abort
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  error_result = Rraise 'a | Rabort abort
End
-/
inductive error_result (α : Type) where
  | Rraise : α → error_result α
  | Rabort : abort → error_result α
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  result = Rval 'a | Rerr ('b error_result)
End
-/
inductive result (α β : Type) where
  | Rval : α → result α β
  | Rerr : error_result β → result α β
deriving Repr, BEq, Inhabited

-- Store types
/- HOL4:
Datatype:
  store_v = Refv 'a | W8array (word8 list) | Varray ('a list) | Thunk thunk_mode 'a
End
-/
inductive store_v (α : Type) where
  | Refv : α → store_v α
  | W8array : List word8 → store_v α
  | Varray : List α → store_v α
  | Thunk : thunk_mode → α → store_v α
deriving Repr, BEq, Inhabited

def store_v_same_type {α : Type} : store_v α → store_v α → Bool
  | .Refv _, .Refv _ => true
  | .W8array _, .W8array _ => true
  | .Varray _, .Varray _ => true
  | .Thunk .NotEvaluated _, .Thunk _ _ => true
  | _, _ => false

abbrev store (α : Type) := List (store_v α)

def store_lookup {α : Type} (l : Nat) (st : List (store_v α)) : Option (store_v α) :=
  if l < st.length then some (EL l st) else none

def store_alloc {α : Type} (val_ : store_v α) (st : List (store_v α)) :
    List (store_v α) × Nat :=
  (st ++ [val_], st.length)

def store_assign {α : Type} (n : Nat) (val_ : store_v α) (st : List (store_v α)) :
    Option (List (store_v α)) :=
  if n < st.length && store_v_same_type (EL n st) val_ then
    some (LUPDATE val_ n st)
  else none

-- Eval state types
abbrev compiler_args := (Nat × Nat) × v × List dec
abbrev compiler_fun := compiler_args → Option (v × List word8 × List word64)

structure eval_decs_state where
  compiler : compiler_fun
  compiler_state : v
  env_id_counter : Nat × Nat × Nat
  decode_decs : v → Option (List dec)

abbrev eval_oracle_fun := Nat → compiler_args

structure eval_oracle_state where
  oracle_field : eval_oracle_fun
  custom_do_eval : List v → eval_oracle_fun →
    Option ((Nat × Nat) × eval_oracle_fun × List dec)
  envs : List (List sem_env)
  generation : Nat

inductive eval_state where
  | EvalDecs : eval_decs_state → eval_state
  | EvalOracle : eval_oracle_state → eval_state

-- The main state type
/- HOL4:
Datatype:
  state = <| clock : num ; refs : v store ; ffi : 'ffi ffi_state
           ; next_type_stamp : num ; next_exn_stamp : num
           ; eval_state : eval_state option |>
End
-/
structure cml_state (ffi : Type) where
  clock : Nat
  refs : store v
  ffi : ffi_state ffi
  next_type_stamp : Nat
  next_exn_stamp : Nat
  eval_state_field : Option eval_state

-- Pattern matching result
/- HOL4:
Datatype:
  match_result = No_match | Match_type_error | Match 'a
End
-/
inductive match_result (α : Type) where
  | No_match : match_result α
  | Match_type_error : match_result α
  | Match : α → match_result α
deriving Repr, BEq, Inhabited

-- Constructor operations
def do_con_check (cenv : env_ctor) (n_opt : Option (cml_id modN conN)) (l : Nat) : Bool :=
  match n_opt with
  | none => true
  | some n => match nsLookup cenv n with
    | none => false
    | some (l', _) => l == l'

def one_con_check (envc : env_ctor) : exp → Bool
  | .Con cn es => do_con_check envc cn es.length
  | _ => true

def build_conv (envC : env_ctor) (cn : Option (cml_id modN conN)) (vs : List v) :
    Option v :=
  match cn with
  | none => some (.Conv none vs)
  | some id_ =>
    match nsLookup envC id_ with
    | none => none
    | some (_, stmp) => some (.Conv (some stmp) vs)

def lit_same_type : lit → lit → Bool
  | .IntLit _, .IntLit _ => true
  | .Char _, .Char _ => true
  | .StrLit _, .StrLit _ => true
  | .Word8 _, .Word8 _ => true
  | .Word64 _, .Word64 _ => true
  | .Float64 _, .Float64 _ => true
  | _, _ => false

def same_type : stamp → stamp → Bool
  | .TypeStamp _ n1, .TypeStamp _ n2 => n1 == n2
  | .ExnStamp _, .ExnStamp _ => true
  | _, _ => false

def same_ctor (s1 s2 : stamp) : Bool := s1 == s2

def ctor_same_type : Option stamp → Option stamp → Bool
  | none, none => true
  | some s1, some s2 => same_type s1 s2
  | _, _ => false

def Boolv (b : Bool) : v :=
  if b then .Conv (some (.TypeStamp (mlstring.strlit "True") bool_type_num)) []
  else .Conv (some (.TypeStamp (mlstring.strlit "False") bool_type_num)) []

-- Pattern matching
/- HOL4:
Definition pmatch_def: ...
End
-/
mutual
partial def pmatch (envC : env_ctor) (s : store v) : pat → v → alist varN v →
    match_result (alist varN v)
  | .Pany, _, env => .Match env
  | .Pvar x, v', env => .Match ((x, v') :: env)
  | .Plit l, .Litv l', env =>
    if l == l' then .Match env
    else if lit_same_type l l' then .No_match
    else .Match_type_error
  | .Pcon (some n) ps, .Conv (some stamp') vs, env =>
    match nsLookup envC n with
    | none => .Match_type_error
    | some (l, stmp) =>
      if same_type stmp stamp' && ps.length == l then
        if same_ctor stmp stamp' then
          if vs.length == l then pmatch_list envC s ps vs env
          else .Match_type_error
        else .No_match
      else .Match_type_error
  | .Pcon none ps, .Conv none vs, env =>
    if ps.length == vs.length then pmatch_list envC s ps vs env
    else .Match_type_error
  | .Pref p, .Loc _ lnum, env =>
    match store_lookup lnum s with
    | none => .Match_type_error
    | some (.Refv v') => pmatch envC s p v' env
    | some _ => .Match_type_error
  | .Pas p i, v', env => pmatch envC s p v' ((i, v') :: env)
  | .Ptannot p _, v', env => pmatch envC s p v' env
  | _, _, _ => .Match_type_error

partial def pmatch_list (envC : env_ctor) (s : store v) :
    List pat → List v → alist varN v → match_result (alist varN v)
  | [], [], env => .Match env
  | p :: ps, v' :: vs, env =>
    match pmatch envC s p v' env with
    | .No_match =>
      match pmatch_list envC s ps vs env with
      | .No_match => .No_match
      | .Match_type_error => .Match_type_error
      | .Match _ => .No_match
    | .Match_type_error => .Match_type_error
    | .Match env' => pmatch_list envC s ps vs env'
  | _, _, _ => .Match_type_error
end

def can_pmatch_all (envC : env_ctor) (refs : store v) : List pat → v → Bool
  | [], _ => true
  | p :: ps, v' =>
    if (match pmatch envC refs p v' [] with | .Match_type_error => true | _ => false) then false
    else can_pmatch_all envC refs ps v'

-- Recursive env building
def build_rec_env (funs : List (varN × varN × exp)) (cl_env : sem_env)
    (add_to_env : «namespace» modN varN v) : «namespace» modN varN v :=
  funs.foldr (fun (f, _, _) env' => nsBind f (.Recclosure cl_env funs f) env') add_to_env

def find_recfun (n : varN) : List (varN × varN × exp) → Option (varN × exp)
  | [] => none
  | (f, x, e) :: funs' => if f == n then some (x, e) else find_recfun n funs'

-- Equality
/- HOL4:
Datatype:
  eq_result = Eq_val bool | Eq_type_error
End
-/
inductive eq_result where
  | Eq_val : Bool → eq_result
  | Eq_type_error : eq_result
deriving Repr, BEq, Inhabited

mutual
partial def do_eq : v → v → eq_result
  | .Litv l1, .Litv l2 =>
    if lit_same_type l1 l2 then .Eq_val (l1 == l2) else .Eq_type_error
  | .Loc b1 l1, .Loc b2 l2 =>
    if b1 && b2 then .Eq_val (l1 == l2) else .Eq_type_error
  | .Conv cn1 vs1, .Conv cn2 vs2 =>
    if cn1 == cn2 && vs1.length == vs2.length then do_eq_list vs1 vs2
    else if ctor_same_type cn1 cn2 then .Eq_val false
    else .Eq_type_error
  | .Vectorv vs1, .Vectorv vs2 =>
    if vs1.length == vs2.length then do_eq_list vs1 vs2 else .Eq_val false
  | .Closure _ _ _, .Closure _ _ _ => .Eq_val true
  | .Closure _ _ _, .Recclosure _ _ _ => .Eq_val true
  | .Recclosure _ _ _, .Closure _ _ _ => .Eq_val true
  | .Recclosure _ _ _, .Recclosure _ _ _ => .Eq_val true
  | .Env _ (gen1, id1), .Env _ (gen2, id2) => .Eq_val (gen1 == gen2 && id1 == id2)
  | _, _ => .Eq_type_error

partial def do_eq_list : List v → List v → eq_result
  | [], [] => .Eq_val true
  | v1 :: vs1, v2 :: vs2 =>
    match do_eq v1 v2 with
    | .Eq_val r => if !r then .Eq_val false else do_eq_list vs1 vs2
    | .Eq_type_error => .Eq_type_error
  | _, _ => .Eq_val false
end

-- Function application
def do_opapp (vs : List v) : Option (sem_env × exp) :=
  match vs with
  | [.Closure env n e, val_] =>
    some (.mk (nsBind n val_ env.v_) env.c, e)
  | [.Recclosure env' funs n', val_] =>
    if ALL_DISTINCT (funs.map fun (f, _, _) => f) then
      match find_recfun n' funs with
      | none => none
      | some (n, e) =>
        some (.mk (nsBind n val_ (build_rec_env funs env' env'.v_)) env'.c, e)
    else none
  | _ => none

-- Value/list conversions
partial def v_to_list : v → Option (List v)
  | .Conv (some stmp) [] =>
    if stmp == .TypeStamp (mlstring.strlit "[]") list_type_num then some [] else none
  | .Conv (some stmp) [v1, v2] =>
    if stmp == .TypeStamp (mlstring.strlit "::") list_type_num then
      match v_to_list v2 with
      | none => none
      | some vs => some (v1 :: vs)
    else none
  | _ => none

def list_to_v : List v → v
  | [] => .Conv (some (.TypeStamp (mlstring.strlit "[]") list_type_num)) []
  | x :: xs => .Conv (some (.TypeStamp (mlstring.strlit "::") list_type_num)) [x, list_to_v xs]

partial def v_to_char_list : v → Option (List Char)
  | .Conv (some stmp) [] =>
    if stmp == .TypeStamp (mlstring.strlit "[]") list_type_num then some [] else none
  | .Conv (some stmp) [.Litv (.Char c), v'] =>
    if stmp == .TypeStamp (mlstring.strlit "::") list_type_num then
      match v_to_char_list v' with
      | none => none
      | some cs => some (c :: cs)
    else none
  | _ => none

def vs_to_string : List v → Option mlstring
  | [] => some (mlstring.strlit "")
  | .Litv (.StrLit s1) :: vs =>
    match vs_to_string vs with
    | none => none
    | some s2 => some (strcat s1 s2)
  | _ :: _ => none

def nat_to_v (n : Nat) : v := .Litv (.IntLit (Int.ofNat n))

def maybe_all_list {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some x :: vs =>
    match maybe_all_list vs with
    | none => none
    | some xs => some (x :: xs)

def v_to_word8 : v → Option word8
  | .Litv (.Word8 w) => some w
  | _ => none

def v_to_word8_list (val_ : v) : Option (List word8) :=
  match v_to_list val_ with
  | none => none
  | some xs => maybe_all_list (xs.map v_to_word8)

def v_to_word64 : v → Option word64
  | .Litv (.Word64 w) => some w
  | _ => none

def v_to_word64_list (val_ : v) : Option (List word64) :=
  match v_to_list val_ with
  | none => none
  | some xs => maybe_all_list (xs.map v_to_word64)

-- Shift lookups
def shift8_lookup : shift → word8 → Nat → word8
  | .Lsl => word_lsl_8
  | .Lsr => word_lsr_8
  | .Asr => word_asr_8
  | .Ror => word_ror_8

def shift64_lookup : shift → word64 → Nat → word64
  | .Lsl => word_lsl_64
  | .Lsr => word_lsr_64
  | .Asr => word_asr_64
  | .Ror => word_ror_64

/- HOL4:
Datatype:
  exp_or_val = Exp exp | Val v
End
-/
inductive exp_or_val where
  | Exp : exp → exp_or_val
  | Val : v → exp_or_val

-- Logical operations
def do_log (l : lop) (val_ : v) (e : exp) : Option exp_or_val :=
  if (l == .Andalso && val_ == Boolv true) || (l == .Orelse && val_ == Boolv false) then
    some (.Exp e)
  else if (l == .Andalso && val_ == Boolv false) || (l == .Orelse && val_ == Boolv true) then
    some (.Val val_)
  else none

def do_if (val_ : v) (e1 e2 : exp) : Option exp :=
  if val_ == Boolv true then some e1
  else if val_ == Boolv false then some e2
  else none

-- Type definition building
def build_constrs (stmp : Nat) (condefs : List (conN × List ast_t)) :
    List (conN × Nat × stamp) :=
  condefs.map fun (cn, ts) => (cn, ts.length, stamp.TypeStamp cn stmp)

def build_tdefs (next_stamp : Nat) : type_def → «namespace» modN conN (Nat × stamp)
  | [] => alist_to_ns []
  | (_, _, condefs) :: tds =>
    nsAppend (build_tdefs (next_stamp + 1) tds)
      (alist_to_ns ((build_constrs next_stamp condefs).reverse))

def check_dup_ctors : List tvarN × typeN × List (conN × List ast_t) → Bool
  | (_, _, condefs) =>
    ALL_DISTINCT (condefs.map fun (n, _) => n)

def combine_dec_result {α : Type} (env : sem_env) :
    result sem_env α → result sem_env α
  | .Rval env' => .Rval (.mk (nsAppend env'.v_ env.v_) (nsAppend env'.c env.c))
  | .Rerr e => .Rerr e

def extend_dec_env (new_env env : sem_env) : sem_env :=
  .mk (nsAppend new_env.v_ env.v_) (nsAppend new_env.c env.c)

/- HOL4:
Datatype:
  dest_thunk_ret = BadRef | NotThunk | IsThunk thunk_mode v
End
-/
inductive dest_thunk_ret where
  | BadRef : dest_thunk_ret
  | NotThunk : dest_thunk_ret
  | IsThunk : thunk_mode → v → dest_thunk_ret

def dest_thunk : List v → store v → dest_thunk_ret
  | [.Loc _ n], st =>
    match store_lookup n st with
    | none => .BadRef
    | some (.Thunk .Evaluated val_) => .IsThunk .Evaluated val_
    | some (.Thunk .NotEvaluated val_) => .IsThunk .NotEvaluated val_
    | some _ => .NotThunk
  | _, _ => .NotThunk

def update_thunk : List v → store v → List v → Option (store v)
  | [.Loc _ n], st, [val_] =>
    match dest_thunk [val_] st with
    | .NotThunk => store_assign n (.Thunk .Evaluated val_) st
    | _ => none
  | _, _, _ => none

-- Eval-related (complex, stubbed out for brevity of key parts)

def lookup_env (s : eval_oracle_state) (ij : Nat × Nat) : Option sem_env :=
  match oEL ij.1 s.envs with
  | none => none
  | some gen_envs => oEL ij.2 gen_envs

def add_decs_generation (s : eval_decs_state) : eval_decs_state :=
  match s.env_id_counter with
  | (_, _, next_gen) =>
    { s with env_id_counter := (next_gen, 0, next_gen + 1) }

def add_env_generation (s : eval_oracle_state) : eval_oracle_state :=
  { s with generation := s.envs.length, envs := s.envs ++ [[]] }

def declare_env (es : Option eval_state) (env : sem_env) :
    Option (v × Option eval_state) :=
  match es with
  | none => none
  | some (.EvalDecs s) =>
    match s.env_id_counter with
    | (cur_gen, next_id, next_gen) =>
      some (.Env env (cur_gen, next_id),
            some (.EvalDecs { s with env_id_counter := (cur_gen, next_id + 1, next_gen) }))
  | some (.EvalOracle s') =>
    match oEL s'.generation s'.envs with
    | none => none
    | some gen_envs =>
      some (.Conv none [nat_to_v s'.generation, nat_to_v gen_envs.length],
            some (.EvalOracle
              { s' with envs := LUPDATE (gen_envs ++ [env]) s'.generation s'.envs }))

def concrete_v : v → Bool := sorry
def concrete_v_list : List v → Bool := sorry
def compiler_agrees : compiler_fun → compiler_args → v × v × v → Bool := sorry
def do_eval : List v → Option eval_state →
    Option (sem_env × List dec × Option eval_state) := sorry
def reset_env_generation : Option eval_state → Option eval_state →
    Option eval_state := sorry

-- copy_array, ws_to_chars, chars_to_ws, xor_bytes, thunk_op, check_type, do_test, do_arith,
-- do_conversion, do_app -- all large case-analysis functions
def copy_array {α : Type} (src_off : List α × Int) (len : Int)
    (d : Option (List α × Int)) : Option (List α) := sorry

def ws_to_chars (ws : List word8) : List Char :=
  ws.map fun w => CHR (w2n_8 w)

def chars_to_ws (cs : List Char) : List word8 :=
  cs.map fun c => i2w_8 (Int.ofNat (ORD c))

def xor_bytes : List word8 → List word8 → Option (List word8)
  | [], bs2 => some bs2
  | _, [] => none
  | b1 :: bs1, b2 :: bs2 =>
    match xor_bytes bs1 bs2 with
    | none => none
    | some rest => some (word_xor_8 b1 b2 :: rest)

def check_type (ty : prim_type) (val_ : v) : Bool := sorry

def do_test : test → prim_type → v → v → eq_result := sorry
def do_arith : arith → prim_type → List v → Option (v ⊕ v) := sorry
def do_conversion : v → prim_type → prim_type → Option (v ⊕ v) := sorry

/- HOL4:
Definition do_app_def:
  do_app (s: v store_v list, t: 'ffi ffi_state) op vs = ...
End

  This is a very large (~200 line) case analysis. We stub it out.
-/
def do_app {ffi : Type} (st : store v × ffi_state ffi) (o_ : op) (vs : List v) :
    Option ((store v × ffi_state ffi) × result v v) := sorry
