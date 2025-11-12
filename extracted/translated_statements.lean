-- Auto-generated LEAN 4 file from HOL4 translation
-- Generated using Gemini API

-- Original HOL4 Datatype: lit
-- lit =
    IntLit int
  | Char char
  | StrLit string
  | Word8 word8
  | Word64 word64
  | Float64 word64
inductive lit where
  | IntLit (i : Int) : lit
  | Char (c : Char) : lit
  | StrLit (s : String) : lit
  | Word8 (w : UInt8) : lit
  | Word64 (w : UInt64) : lit
  | Float64 (w : UInt64) : lit

-- Original HOL4 Datatype: opn
-- opn = Plus | Minus | Times | Divide | Modulo
inductive opn where
  | Plus | Minus | Times | Divide | Modulo

-- Original HOL4 Datatype: opb
-- opb = Lt | Gt | Leq | Geq
inductive opb where
  | Lt | Gt | Leq | Geq

-- Original HOL4 Datatype: opw
-- opw = Andw | Orw | Xor | Add | Sub
inductive opw where
  | Andw | Orw | Xor | Add | Sub

-- Original HOL4 Datatype: shift
-- shift = Lsl | Lsr | Asr | Ror
inductive shift where
  | Lsl | Lsr | Asr | Ror

-- Original HOL4 Datatype: fp_cmp
-- fp_cmp = FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal
inductive fp_cmp where
  | FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal

-- Original HOL4 Datatype: fp_uop
-- fp_uop = FP_Abs | FP_Neg | FP_Sqrt
inductive fp_uop where
  | FP_Abs | FP_Neg | FP_Sqrt

-- Original HOL4 Datatype: fp_bop
-- fp_bop = FP_Add | FP_Sub | FP_Mul | FP_Div
inductive fp_bop where
  | FP_Add | FP_Sub | FP_Mul | FP_Div

-- Original HOL4 Datatype: fp_top
-- fp_top = FP_Fma
inductive fp_top where
  | FP_Fma

-- Original HOL4 Datatype: word_size
-- word_size = W8 | W64
inductive word_size where
  | W8 | W64

-- Original HOL4 Datatype: thunk_mode
-- thunk_mode = Evaluated | NotEvaluated
inductive thunk_mode where
  | Evaluated | NotEvaluated

-- Original HOL4 Datatype: thunk_op
-- thunk_op =
    AllocThunk thunk_mode
  | UpdateThunk thunk_mode
  | ForceThunk
inductive thunk_op where
  | AllocThunk (m : thunk_mode) : thunk_op
  | UpdateThunk (m : thunk_mode) : thunk_op
  | ForceThunk : thunk_op

-- Original HOL4 Datatype: op
-- op =
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
inductive op where
  | Opn (o : opn) : op
  | Opb (o : opb) : op
  | Opw (ws : word_size) (o : opw) : op
  | Shift (ws : word_size) (s : shift) (n : Nat) : op
  | Equality : op
  | FP_cmp (c : fp_cmp) : op
  | FP_uop (u : fp_uop) : op
  | FP_bop (b : fp_bop) : op
  | FP_top (t : fp_top) : op
  | FpFromWord : op
  | FpToWord : op
  | Opapp : op
  | Opassign : op
  | Opref : op
  | Opderef : op
  | Aw8alloc : op
  | Aw8sub : op
  | Aw8length : op
  | Aw8update : op
  | WordFromInt (ws : word_size) : op
  | WordToInt (ws : word_size) : op
  | CopyStrStr : op
  | CopyStrAw8 : op
  | CopyAw8Str : op
  | CopyAw8Aw8 : op
  | XorAw8Str_unsafe : op
  | Ord : op
  | Chr : op
  | Chopb (o : opb) : op
  | Implode : op
  | Explode : op
  | Strsub : op
  | Strlen : op
  | Strcat : op
  | VfromList : op
  | Vsub : op
  | Vlength : op
  | Aalloc : op
  | AallocEmpty : op
  | AallocFixed : op
  | Asub : op
  | Alength : op
  | Aupdate : op
  | Asub_unsafe : op
  | Aupdate_unsafe : op
  | Aw8sub_unsafe : op
  | Aw8update_unsafe : op
  | ThunkOp (t : thunk_op) : op
  | ListAppend : op
  | ConfigGC : op
  | FFI (s : String) : op
  | Eval : op
  | Env_id : op

-- Original HOL4 Datatype: op_class
-- op_class =
    EvalOp (* Eval primitive *)
  | FunApp (* function application *)
  | Force (* forcing a thunk *)
  | Simple (* arithmetic operation, no finite-precision/reals *)
inductive op_class where
  | EvalOp | FunApp | Force | Simple

-- Original HOL4 Datatype: lop
-- lop = And | Or
inductive lop where
  | And | Or

-- Original HOL4 Datatype: ast_t
-- ast_t =
  (* Type variables that the user writes down ('a, 'b, etc.) *)
    Atvar tvarN
  (* Function type *)
  | Atfun ast_t ast_t
  (* Tuple type *)
  | Attup (ast_t list)
  (* Type constructor applications.
    0-ary type applications represent unparameterised types (e.g., num or string) *)
  | Atapp (ast_t list) ((modN, typeN) id)
inductive ast_t where
  | Atvar (v : tvarN) : ast_t
  | Atfun (dom : ast_t) (ran : ast_t) : ast_t
  | Attup (ts : List ast_t) : ast_t
  | Atapp (ts : List ast_t) (i : id modN typeN) : ast_t

-- Original HOL4 Datatype: pat
-- pat =
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
inductive pat where
  | Pany : pat
  | Pvar (v : varN) : pat
  | Plit (l : lit) : pat
  | Pcon (c : Option (id modN conN)) (ps : List pat) : pat
  | Pref (p : pat) : pat
  | Pas (p : pat) (v : varN) : pat
  | Ptannot (p : pat) (t : ast_t) : pat

-- Original HOL4 Datatype: exp
-- exp =
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
inductive exp where
  | Raise (e : exp) : exp
  | Handle (e : exp) (cases : List (pat × exp)) : exp
  | Lit (l : lit) : exp
  | Con (c : Option (id modN conN)) (es : List exp) : exp
  | Var (v : id modN varN) : exp
  | Fun (v : varN) (body : exp) : exp
  | App (o : op) (args : List exp) : exp
  | Log (o : lop) (e1 e2 : exp) : exp
  | If (c e1 e2 : exp) : exp
  | Mat (e : exp) (cases : List (pat × exp)) : exp
  | Let (v : Option varN) (b e : exp) : exp
  | Letrec (bindings : List (varN × varN × exp)) (body : exp) : exp
  | Tannot (e : exp) (t : ast_t) : exp
  | Lannot (e : exp) (l : locs) : exp

-- Original HOL4 Datatype: dec
-- dec =
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
inductive dec where
  | Dlet (l : locs) (p : pat) (e : exp) : dec
  | Dletrec (l : locs) (bindings : List (varN × varN × exp)) : dec
  | Dtype (l : locs) (td : type_def) : dec
  | Dtabbrev (l : locs) (tvs : List tvarN) (tn : typeN) (t : ast_t) : dec
  | Dexn (l : locs) (cn : conN) (ts : List ast_t) : dec
  | Dmod (m : modN) (decs : List dec) : dec
  | Dlocal (local_decs : List dec) (visible_decs : List dec) : dec
  | Denv (tv : tvarN) : dec

-- Original HOL4 Datatype: id
-- id = Short 'n | Long 'm id
universe u v
inductive id (m : Type u) (n : Type v) where
  | Short (val : n) : id m n
  | Long (mod_name : m) (rest : id m n) : id m n

-- Original HOL4 Datatype: namespace
-- namespace =
    Bind (('n,'v) alist) (('m,namespace) alist)
universe u v w
inductive namespace (m : Type u) (n : Type v) (val : Type w) where
  | Bind (vars : List (n × val)) (mods : List (m × namespace m n val)) : namespace m n val

-- Original HOL4 Definition: isFpBool_def
-- isFpBool op = case op of FP_cmp _ => T | _ => F
def isFpBool (o : op) : Bool :=
  match o with
  | op.FP_cmp _ => true
  | _ => false

-- Original HOL4 Definition: pat_bindings_def
-- pat_bindings Pany already_bound = already_bound ∧
  pat_bindings (Pvar n) already_bound = n::already_bound ∧
  pat_bindings (Plit l) already_bound = already_bound ∧
  pat_bindings (Pcon v0 ps) already_bound = pats_bindings ps already_bound ∧
  pat_bindings (Pref p) already_bound = pat_bindings p already_bound ∧
  pat_bindings (Pas p i) already_bound = pat_bindings p (i::already_bound) ∧
  pat_bindings (Ptannot p v1) already_bound = pat_bindings p already_bound ∧
  pats_bindings [] already_bound = already_bound ∧
  pats_bindings (p::ps) already_bound =
  pats_bindings ps (pat_bindings p already_bound)
mutual
def pat_bindings (p : pat) (already_bound : List varN) : List varN :=
  match p with
  | pat.Pany => already_bound
  | pat.Pvar n => n :: already_bound
  | pat.Plit _ => already_bound
  | pat.Pcon _ ps => pats_bindings ps already_bound
  | pat.Pref p' => pat_bindings p' already_bound
  | pat.Pas p' i => pat_bindings p' (i :: already_bound)
  | pat.Ptannot p' _ => pat_bindings p' already_bound

def pats_bindings (ps : List pat) (already_bound : List varN) : List varN :=
  match ps with
  | [] => already_bound
  | p :: rest => pats_bindings rest (pat_bindings p already_bound)
end

-- Original HOL4 Definition: Seqs_def
-- Seqs [] = Con NONE [] ∧
  Seqs (x::xs) = Let NONE x (Seqs xs)
def Seqs : List exp → exp
  | [] => exp.Con none []
  | x :: xs => exp.Let none x (Seqs xs)

-- Original HOL4 Definition: Apps_def
-- Apps f [] = f ∧
  Apps f (x::xs) = Apps (App Opapp [f; x]) xs
def Apps (f : exp) : List exp → exp
  | [] => f
  | x :: xs => Apps (exp.App op.Opapp [f, x]) xs

-- Original HOL4 Definition: Funs_def
-- Funs [] e = e ∧
  Funs (x::xs) e = Fun x (Funs xs e)
def Funs : List varN → exp → exp
  | [], e => e
  | x :: xs, e => exp.Fun x (Funs xs e)

-- Original HOL4 Definition: alist_rel_restr_def
-- (alist_rel_restr R l1 l2 [] ⇔ T) ∧
  (alist_rel_restr R l1 l2 (k1::keys) ⇔
    case ALOOKUP l1 k1 of
    | NONE => F
    | SOME v1 =>
      case ALOOKUP l2 k1 of
      | NONE => F
      | SOME v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys)
def alist_rel_restr {κ α β} [BEq κ] (R : κ → α → β → Prop) (l1 : List (κ × α)) (l2 : List (κ × β)) : List κ → Prop
  | [] => True
  | k1 :: keys =>
    match l1.lookup k1 with
    | none => False
    | some v1 =>
      match l2.lookup k1 with
      | none => False
      | some v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys

-- Original HOL4 Definition: alistSub_def
-- alistSub R e1 e2 ⇔ alist_rel_restr R e1 e2 (MAP FST e1)
def alistSub {κ α β} [BEq κ] (R : κ → α → β → Prop) (e1 : List (κ × α)) (e2 : List (κ × β)) : Prop :=
  alist_rel_restr R e1 e2 (e1.map Prod.fst)

-- Original HOL4 Definition: nsSub_compute_def
-- nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ⇔
    alistSub (\k v1 v2. R (mk_id (REVERSE path) k) v1 v2) e1V e2V ∧
    alistSub (\k v1 v2. nsSub_compute (k::path) R v1 v2) e1M e2M
Termination
  wf_rel_tac `measure (\(p,r,env,_). namespace_size (\x.0) (\x.0) (\x.0) env)`
 >> rw []
 >> Induct_on `e1M`
 >> rw [namespace_size_def]
 >> PairCases_on `h`
 >> fs [ALOOKUP_def]
 >> every_case_tac
 >> fs []
 >> rw [namespace_size_def,basicSizeTheory.pair_size_def]
def nsSub_compute {m n v} [BEq n] [BEq m] (path : List m) (R : id m n → v → v → Prop) : namespace m n v → namespace m n v → Prop :=
  fun (namespace.Bind e1V e1M) (namespace.Bind e2V e2M) =>
    alistSub (fun k v1 v2 => R (mk_id path.reverse k) v1 v2) e1V e2V ∧
    alistSub (fun k v1 v2 => nsSub_compute (k :: path) R v1 v2) e1M e2M

-- Original HOL4 Definition: mk_id_def
-- mk_id [] n = Short n ∧
  mk_id (mn::mns) n = Long mn (mk_id mns n)
def mk_id {m n} : List m → n → id m n
  | [], val => id.Short val
  | mod_name :: rest, val => id.Long mod_name (mk_id rest val)

-- Original HOL4 Definition: id_to_n_def
-- id_to_n (Short n) = n ∧
 id_to_n (Long _ id) = id_to_n id
def id_to_n {m n} : id m n → n
  | id.Short val => val
  | id.Long _ i => id_to_n i

-- Original HOL4 Definition: id_to_mods_def
-- id_to_mods (Short _) = [] ∧
  id_to_mods (Long mn id) = mn::id_to_mods id
def id_to_mods {m n} : id m n → List m
  | id.Short _ => []
  | id.Long mn i => mn :: id_to_mods i

-- Original HOL4 Definition: nsLookup_def
-- nsLookup ((Bind v m):('m,'n,'v)namespace) (Short n) =
    ALOOKUP v n ∧
  nsLookup (Bind v m) (Long mn id) =
    case ALOOKUP m mn of
    | NONE => NONE
    | SOME env => nsLookup env id
def nsLookup {m n v} [BEq n] [BEq m] : namespace m n v → id m n → Option v
  | namespace.Bind vars _, id.Short val => vars.lookup val
  | namespace.Bind _ mods, id.Long mn i =>
    match mods.lookup mn with
    | none => none
    | some env => nsLookup env i

-- Original HOL4 Definition: nsLookupMod_def
-- nsLookupMod e [] = SOME (e:('m,'n,'v)namespace) ∧
  nsLookupMod (Bind v m) (mn::path) =
  case ALOOKUP m mn of NONE => NONE | SOME env => nsLookupMod env path
def nsLookupMod {m n v} [BEq m] : namespace m n v → List m → Option (namespace m n v)
  | _, [] => some e
  | namespace.Bind _ mods, mn :: path =>
    match mods.lookup mn with
    | none => none
    | some env' => nsLookupMod env' path

-- Original HOL4 Definition: nsEmpty_def
-- nsEmpty = Bind [] []
def nsEmpty {m n v} : namespace m n v := namespace.Bind [] []

-- Original HOL4 Definition: nsAppend_def
-- nsAppend (Bind v1 m1) (Bind v2 m2) = Bind (v1 ++ v2) (m1 ++ m2)
def nsAppend {m n v} : namespace m n v → namespace m n v → namespace m n v
  | namespace.Bind v1 m1, namespace.Bind v2 m2 => namespace.Bind (v1 ++ v2) (m1 ++ m2)

-- Original HOL4 Definition: nsLift_def
-- nsLift mn env = Bind [] [(mn,env)]
def nsLift {m n v} (mn : m) (env : namespace m n v) : namespace m n v :=
  namespace.Bind [] [(mn, env)]

-- Original HOL4 Definition: alist_to_ns_def
-- alist_to_ns a = Bind a []
def alist_to_ns {m n v} (a : List (n × v)) : namespace m n v :=
  namespace.Bind a []

-- Original HOL4 Definition: nsBind_def
-- nsBind k x (Bind v m) = Bind ((k,x)::v) m
def nsBind {m n v} (k : n) (x : v) : namespace m n v → namespace m n v
  | namespace.Bind vars mods => namespace.Bind ((k, x) :: vars) mods

-- Original HOL4 Definition: nsBindList_def
-- nsBindList l e = FOLDR (λ(x,v) e. nsBind x v e) e l
def nsBindList {m n v} (l : List (n × v)) (e : namespace m n v) : namespace m n v :=
  l.foldr (fun (k, val) acc => nsBind k val acc) e

-- Original HOL4 Definition: nsOptBind_def
-- nsOptBind n x env = case n of NONE => env | SOME n => nsBind n x env
def nsOptBind {m n v} (n_opt : Option n) (x : v) (env : namespace m n v) : namespace m n v :=
  match n_opt with
  | none => env
  | some k => nsBind k x env

-- Original HOL4 Definition: nsSing_def
-- nsSing n x = Bind [(n,x)] []
def nsSing {m n v} (k : n) (x : v) : namespace m n v :=
  namespace.Bind [(k, x)] []

-- Original HOL4 Definition: nsSub_def
-- nsSub r env1 env2 ⇔
     (∀id v1.
        nsLookup env1 id = SOME v1 ⇒
        ∃v2. nsLookup env2 id = SOME v2 ∧ r id v1 v2) ∧
     ∀path. nsLookupMod env2 path = NONE ⇒ nsLookupMod env1 path = NONE
def nsSub {m n v} [BEq n] [BEq m] (r : id m n → v → v → Prop) (env1 env2 : namespace m n v) : Prop :=
  (∀ i v1, nsLookup env1 i = some v1 → ∃ v2, nsLookup env2 i = some v2 ∧ r i v1 v2) ∧
  (∀ path, nsLookupMod env2 path = none → nsLookupMod env1 path = none)

-- Original HOL4 Definition: nsAll_def
-- nsAll f env ⇔ ∀id v. nsLookup env id = SOME v ⇒ f id v
def nsAll {m n v} [BEq n] [BEq m] (f : id m n → v → Prop) (env : namespace m n v) : Prop :=
  ∀ i val, nsLookup env i = some val → f i val

-- Original HOL4 Definition: nsAll2_def
-- nsAll2 r env1 env2 ⇔
    nsSub r env1 env2 ∧ nsSub (λx y z. r x z y) env2 env1
def nsAll2 {m n v} [BEq n] [BEq m] (r : id m n → v → v → Prop) (env1 env2 : namespace m n v) : Prop :=
  nsSub r env1 env2 ∧ nsSub (fun i v2 v1 => r i v1 v2) env2 env1

-- Original HOL4 Definition: nsDom_def
-- nsDom (env:('m,'n,'v)namespace) =
     {n | (v,n) | v ∈ 𝕌(:φ) ∧ n ∈ 𝕌(:(ν, ξ) id) ∧ nsLookup env n = SOME v}
def nsDom {m n v} [BEq n] [BEq m] (env : namespace m n v) : Set (id m n) :=
  { i | ∃ val, nsLookup env i = some val }

-- Original HOL4 Definition: nsDomMod_def
-- nsDomMod (env:('m,'n,'v)namespace) =
     {n | (v,n) | v ∈ 𝕌(:(ν, ξ, φ) namespace) ∧ n ∈ 𝕌(:ν list) ∧
                  nsLookupMod env n = SOME v}
def nsDomMod {m n v} [BEq m] (env : namespace m n v) : Set (List m) :=
  { p | ∃ ns, nsLookupMod env p = some ns }

-- Original HOL4 Definition: nsMap_def
-- nsMap (f:'v -> 'w) ((Bind v m):('m,'n,'v)namespace) =
    Bind (MAP (λ(n,x). (n,f x)) v) (MAP (λ(mn,e). (mn,nsMap f e)) m)
def nsMap {m n v w} (f : v → w) : namespace m n v → namespace m n w
  | namespace.Bind vars mods =>
    let vars' := vars.map (fun (name, val) => (name, f val));
    let mods' := mods.map (fun (name, ns) => (name, nsMap f ns));
    namespace.Bind vars' mods'

-- Original HOL4 Theorem: mk_id_surj
-- !id. ?p n. id = mk_id p n
theorem mk_id_surj {m n} (i : id m n) : ∃ (p : List m) (val : n), i = mk_id p val := sorry

-- Original HOL4 Theorem: mk_id_thm
-- !id. mk_id (id_to_mods id) (id_to_n id) = id
theorem mk_id_thm {m n} (i : id m n) : mk_id (id_to_mods i) (id_to_n i) = i := sorry

-- Original HOL4 Theorem: nsSub_mono2
-- (!x y z. nsLookup e1 x = SOME y ∧ nsLookup e2 x = SOME z ∧ R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2)
theorem nsSub_mono2 {m n v} [BEq n] [BEq m] {R1 R2 : id m n → v → v → Prop} {e1 e2 : namespace m n v}
  (h : ∀ x y z, nsLookup e1 x = some y → nsLookup e2 x = some z → R1 x y z → R2 x y z) :
  nsSub R1 e1 e2 → nsSub R2 e1 e2 := sorry

-- Original HOL4 Theorem: nsLookup_Bind_v_some
-- nsLookup (Bind v []) k = SOME x ⇔
   ∃y. k = Short y ∧ ALOOKUP v y = SOME x
theorem nsLookup_Bind_v_some {m n v} [BEq n] [BEq m] (v_list : List (n × v)) (k : id m n) (x : v) :
  nsLookup (namespace.Bind v_list []) k = some x ↔ ∃ y, k = id.Short y ∧ v_list.lookup y = some x := sorry

-- Original HOL4 Theorem: nsLookup_to_nsLookupMod
-- !n v t.
    nsLookup n v = SOME t
    ⇒
    ?m. nsLookupMod n (id_to_mods v) = SOME m ∧ nsLookup m (Short (id_to_n v)) = SOME t
theorem nsLookup_to_nsLookupMod {m n v} [BEq n] [BEq m] (ns : namespace m n v) (i : id m n) (t : v) :
  nsLookup ns i = some t → ∃ m', nsLookupMod ns (id_to_mods i) = some m' ∧ nsLookup m' (id.Short (id_to_n i)) = some t := sorry

-- Original HOL4 Theorem: nsLookup_alist_to_ns_some
-- !l id v. nsLookup (alist_to_ns l) id = SOME v ⇔ ?x'. id = Short x' ∧ ALOOKUP l x' = SOME v
theorem nsLookup_alist_to_ns_some {m n v} [BEq n] [BEq m] (l : List (n × v)) (i : id m n) (val : v) :
  nsLookup (alist_to_ns l) i = some val ↔ ∃ x', i = id.Short x' ∧ l.lookup x' = some val := sorry

-- Original HOL4 Theorem: nsLookup_alist_to_ns_none
-- !l id. nsLookup (alist_to_ns l) id = NONE ⇔ !x'. id = Short x' ⇒ ALOOKUP l x' = NONE
theorem nsLookup_alist_to_ns_none {m n v} [BEq n] [BEq m] (l : List (n × v)) (i : id m n) :
  nsLookup (alist_to_ns l) i = none ↔ ∀ x', i = id.Short x' → l.lookup x' = none := sorry

-- Original HOL4 Theorem: nsLookup_nsLift
-- !mn e id.
    nsLookup (nsLift mn e) id =
    case id of
    | Long mn' id' =>
      if mn = mn' then
        nsLookup e id'
      else
        NONE
    | Short _ => NONE
theorem nsLookup_nsLift {m n v} [BEq n] [BEq m] [DecidableEq m] (mn : m) (e : namespace m n v) (i : id m n) :
  nsLookup (nsLift mn e) i =
    match i with
    | id.Long mn' i' => if mn = mn' then nsLookup e i' else none
    | id.Short _ => none := sorry

-- Original HOL4 Theorem: nsLookupMod_nsLift
-- !mn e path.
    nsLookupMod (nsLift mn e) path =
    case path of
    | [] => SOME (nsLift mn e)
    | (mn'::path') =>
      if mn = mn' then
        nsLookupMod e path'
      else
        NONE
theorem nsLookupMod_nsLift {m n v} [BEq m] [DecidableEq m] (mn : m) (e : namespace m n v) (path : List m) :
  nsLookupMod (nsLift mn e) path =
    match path with
    | [] => some (nsLift mn e)
    | mn' :: path' => if mn = mn' then nsLookupMod e path' else none := sorry

-- Original HOL4 Theorem: nsLookup_nsAppend_none
-- ∀e1 id e2.
    nsLookup (nsAppend e1 e2) id = NONE
    ⇔
    (nsLookup e1 id = NONE ∧
     (nsLookup e2 id = NONE ∨
      ?p1 p2 e3. p1 ≠ [] ∧ id_to_mods id = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3))
theorem nsLookup_nsAppend_none {m n v} [BEq n] [BEq m] (e1 e2 : namespace m n v) (i : id m n) :
  nsLookup (nsAppend e1 e2) i = none ↔
  (nsLookup e1 i = none ∧
   (nsLookup e2 i = none ∨
    (∃ p1 p2 e3, ¬ p1.isEmpty ∧ id_to_mods i = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3))) := sorry

-- Original HOL4 Theorem: nsLookup_nsAppend_some
-- ∀e1 id e2 v.
    nsLookup (nsAppend e1 e2) id = SOME v
    ⇔
    nsLookup e1 id = SOME v ∨
    (nsLookup e1 id = NONE ∧ nsLookup e2 id = SOME v ∧
     !p1 p2. p1 ≠ [] ∧ id_to_mods id = p1++p2 ⇒ nsLookupMod e1 p1 = NONE)
theorem nsLookup_nsAppend_some {m n v} [BEq n] [BEq m] (e1 e2 : namespace m n v) (i : id m n) (val : v) :
  nsLookup (nsAppend e1 e2) i = some val ↔
  nsLookup e1 i = some val ∨
  (nsLookup e1 i = none ∧ nsLookup e2 i = some val ∧
   (∀ p1 p2, ¬ p1.isEmpty ∧ id_to_mods i = p1 ++ p2 → nsLookupMod e1 p1 = none)) := sorry

-- Original HOL4 Theorem: nsAppend_to_nsBindList
-- !l. nsAppend (alist_to_ns l) e = nsBindList l e
theorem nsAppend_to_nsBindList {m n v} (l : List (n × v)) (e : namespace m n v) :
  nsAppend (alist_to_ns l) e = nsBindList l e := sorry

-- Original HOL4 Theorem: nsLookupMod_nsAppend_none
-- !e1 e2 path.
    nsLookupMod (nsAppend e1 e2) path = NONE
    ⇔
    (nsLookupMod e1 path = NONE ∧
     (nsLookupMod e2 path = NONE ∨
      ?p1 p2 e3. p1 ≠ [] ∧ path = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3))
theorem nsLookupMod_nsAppend_none {m n v} [BEq m] (e1 e2 : namespace m n v) (path : List m) :
  nsLookupMod (nsAppend e1 e2) path = none ↔
  (nsLookupMod e1 path = none ∧
   (nsLookupMod e2 path = none ∨
    (∃ p1 p2 e3, ¬ p1.isEmpty ∧ path = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3))) := sorry

-- Original HOL4 Theorem: nsLookupMod_nsAppend_some
-- !e1 e2 path.
    (nsLookupMod (nsAppend e1 e2) path = SOME x
     ⇔
     if path = [] then x = nsAppend e1 e2 else
     nsLookupMod e1 path = SOME x ∨
      (nsLookupMod e2 path = SOME x ∧
      !p1 p2. p1 ≠ [] ∧ path = p1++p2 ⇒ nsLookupMod e1 p1 = NONE))
theorem nsLookupMod_nsAppend_some {m n v} [BEq m] [DecidableEq (List m)] [DecidableEq (namespace m n v)] (e1 e2 : namespace m n v) (path : List m) (x : namespace m n v) :
  nsLookupMod (nsAppend e1 e2) path = some x ↔
  (if path.isEmpty then x = nsAppend e1 e2 else
   nsLookupMod e1 path = some x ∨
   (nsLookupMod e2 path = some x ∧
    (∀ p1 p2, ¬ p1.isEmpty ∧ path = p1 ++ p2 → nsLookupMod e1 p1 = none))) := sorry

-- Original HOL4 Theorem: nsLookup_nsAll
-- !env x P v. nsAll P env ∧ nsLookup env x = SOME v ⇒ P x v
theorem nsLookup_nsAll {m n v} [BEq n] [BEq m] (env : namespace m n v) (x : id m n) (P : id m n → v → Prop) (val : v) :
  nsAll P env → nsLookup env x = some val → P x val := sorry

-- Original HOL4 Theorem: nsAll_nsAppend
-- !f e1 e2. nsAll f e1 ∧ nsAll f e2 ⇒ nsAll f (nsAppend e1 e2)
theorem nsAll_nsAppend {m n v} [BEq n] [BEq m] (f : id m n → v → Prop) (e1 e2 : namespace m n v) :
  nsAll f e1 → nsAll f e2 → nsAll f (nsAppend e1 e2) := sorry

-- Original HOL4 Theorem: nsAll_nsBind
-- !P x v e. P (Short x) v ∧ nsAll P e ⇒ nsAll P (nsBind x v e)
theorem nsAll_nsBind {m n v} [BEq n] [BEq m] (P : id m n → v → Prop) (x : n) (val : v) (e : namespace m n v) :
  P (id.Short x) val → nsAll P e → nsAll P (nsBind x val e) := sorry

-- Original HOL4 Theorem: nsAll_nsOptBind
-- !P x v e. (x = NONE ∨ ?n. x = SOME n ∧ P (Short n) v) ∧ nsAll P e ⇒ nsAll P (nsOptBind x v e)
theorem nsAll_nsOptBind {m n v} [BEq n] [BEq m] (P : id m n → v → Prop) (x : Option n) (val : v) (e : namespace m n v) :
  (x = none ∨ (∃ n', x = some n' ∧ P (id.Short n') val)) → nsAll P e → nsAll P (nsOptBind x val e) := sorry

-- Original HOL4 Theorem: nsAll_alist_to_ns
-- !R l. EVERY (λ(n,v). R (Short n) v) l ⇒ nsAll R (alist_to_ns l)
theorem nsAll_alist_to_ns {m n v} [BEq n] [BEq m] (R : id m n → v → Prop) (l : List (n × v)) :
  l.Forall (fun (n, v) => R (id.Short n) v) → nsAll R (alist_to_ns l) := sorry

-- Original HOL4 Theorem: nsAll_nsAppend_left
-- !P n1 n2. nsAll P (nsAppend n1 n2) ⇒ nsAll P n1
theorem nsAll_nsAppend_left {m n v} [BEq n] [BEq m] (P : id m n → v → Prop) (n1 n2 : namespace m n v) :
  nsAll P (nsAppend n1 n2) → nsAll P n1 := sorry

-- Original HOL4 Theorem: nsSub_conj
-- !P Q e1 e2. nsSub (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsSub P e1 e2 ∧
  nsSub Q e1 e2
theorem nsSub_conj {m n v} [BEq n] [BEq m] (P Q : id m n → v → v → Prop) (e1 e2 : namespace m n v) :
  nsSub (fun i x y => P i x y ∧ Q i x y) e1 e2 ↔ nsSub P e1 e2 ∧ nsSub Q e1 e2 := sorry

-- Original HOL4 Theorem: nsSub_refl
-- !P R. (!n x. P n x ⇒ R n x x) ⇒ !e. nsAll P e ⇒ nsSub R e e
theorem nsSub_refl {m n v} [BEq n] [BEq m] (P : id m n → v → Prop) (R : id m n → v → v → Prop) :
  (∀ n x, P n x → R n x x) → ∀ e, nsAll P e → nsSub R e e := sorry

-- Original HOL4 Theorem: nsSub_nsBind
-- !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsSub R e1 e2 ⇒ nsSub R (nsBind x v1 e1) (nsBind x v2 e2)
theorem nsSub_nsBind {m n v} [BEq n] [BEq m] (R : id m n → v → v → Prop) (x : n) (v1 v2 : v) (e1 e2 : namespace m n v) :
  R (id.Short x) v1 v2 → nsSub R e1 e2 → nsSub R (nsBind x v1 e1) (nsBind x v2 e2) := sorry

-- Original HOL4 Theorem: nsSub_nsAppend2
-- !R e1 e2 e2'. nsSub R e1 e1 ∧ nsSub R e2 e2' ⇒ nsSub R (nsAppend e1 e2) (nsAppend e1 e2')
theorem nsSub_nsAppend2 {m n v} [BEq n] [BEq m] (R : id m n → v → v → Prop) (e1 e2 e2' : namespace m n v) :
  nsSub R e1 e1 → nsSub R e2 e2' → nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := sorry

-- Original HOL4 Theorem: nsSub_nsAppend_lift
-- !R mn e1 e1' e2 e2'.
    nsSub (\id. R (Long mn id)) e1 e1' ∧
    nsSub R e2 e2'
    ⇒
    nsSub R (nsAppend (nsLift mn e1) e2) (nsAppend (nsLift mn e1') e2')
theorem nsSub_nsAppend_lift {m n v} [BEq n] [BEq m] (R : id m n → v → v → Prop) (mn : m) (e1 e1' e2 e2' : namespace m n v) :
  nsSub (fun i => R (id.Long mn i)) e1 e1' →
  nsSub R e2 e2' →
  nsSub R (nsAppend (nsLift mn e1) e2) (nsAppend (nsLift mn e1') e2') := sorry

-- Original HOL4 Theorem: alist_rel_restr_thm
-- !R e1 e2 keys.
    alist_rel_restr R e1 e2 keys ⇔
      !k. MEM k keys ⇒ ?v1 v2. ALOOKUP e1 k = SOME v1 ∧ ALOOKUP e2 k = SOME v2 ∧ R k v1 v2
theorem alist_rel_restr_thm {κ α β} [BEq κ] (R : κ → α → β → Prop) (e1 : List (κ × α)) (e2 : List (κ × β)) (keys : List κ) :
  alist_rel_restr R e1 e2 keys ↔
  ∀ k ∈ keys, ∃ v1 v2, e1.lookup k = some v1 ∧ e2.lookup k = some v2 ∧ R k v1 v2 := sorry

-- Original HOL4 Theorem: alistSub_cong
-- !l1 l2 l1' l2' R R'.
    l1 = l1' ∧ l2 = l2' ∧ (!n x y. ALOOKUP l1' n = SOME x ∧ ALOOKUP l2' n = SOME y ⇒ R n x y = R' n x y) ⇒
    (alistSub R l1 l2 ⇔ alistSub R' l1' l2')
theorem alistSub_cong {κ α β} [BEq κ] (l1 l1' : List (κ × α)) (l2 l2' : List (κ × β)) (R R' : κ → α → β → Prop) :
  l1 = l1' → l2 = l2' → (∀ n x y, l1'.lookup n = some x → l2'.lookup n = some y → (R n x y ↔ R' n x y)) →
  (alistSub R l1 l2 ↔ alistSub R' l1' l2') := sorry

-- Original HOL4 Theorem: nsLookup_FOLDR_nsLift
-- !e p k. nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Short k)
theorem nsLookup_FOLDR_nsLift {m n v} [BEq n] [BEq m] (e : namespace m n v) (p : List m) (k : n) :
  nsLookup (p.foldr nsLift e) (mk_id p k) = nsLookup e (id.Short k) := sorry

-- Original HOL4 Theorem: nsLookup_FOLDR_nsLift_some
-- !e p id v.
    nsLookup (FOLDR nsLift e p) id = SOME v ⇔
    (p = [] ∧ nsLookup e id = SOME v) ∨
    (p ≠ [] ∧ ?p2 n. id = mk_id (p++p2) n ∧ nsLookup e (mk_id p2 n) = SOME v)
theorem nsLookup_FOLDR_nsLift_some {m n v} [BEq n] [BEq m] (e : namespace m n v) (p : List m) (i : id m n) (val : v) :
  nsLookup (p.foldr nsLift e) i = some val ↔
  (p.isEmpty ∧ nsLookup e i = some val) ∨
  (¬ p.isEmpty ∧ ∃ p2 n', i = mk_id (p ++ p2) n' ∧ nsLookup e (mk_id p2 n') = some val) := sorry

-- Original HOL4 Theorem: nsLookupMod_FOLDR_nsLift_none
-- !e p1 p2. nsLookupMod (FOLDR nsLift e p1) p2 = NONE ⇔
    (IS_PREFIX p1 p2 ∨ IS_PREFIX p2 p1) ⇒
    ?p3. p2 = p1++p3 ∧ nsLookupMod e p3 = NONE
theorem nsLookupMod_FOLDR_nsLift_none {m n v} [BEq m] (e : namespace m n v) (p1 p2 : List m) :
  nsLookupMod (p1.foldr nsLift e) p2 = none ↔
  ((p1.isPrefixOf p2 ∨ p2.isPrefixOf p1) →
   (∃ p3, p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none)) := sorry

-- Original HOL4 Theorem: nsSub_compute_thm_general
-- !p R e1 e2.
    nsSub R (FOLDR nsLift e1 (REVERSE p)) (FOLDR nsLift e2 (REVERSE p)) ⇔
    nsSub_compute p R e1 e2
theorem nsSub_compute_thm_general {m n v} [BEq n] [BEq m] (p : List m) (R : id m n → v → v → Prop) (e1 e2 : namespace m n v) :
  nsSub R (p.reverse.foldr nsLift e1) (p.reverse.foldr nsLift e2) ↔ nsSub_compute p R e1 e2 := sorry

-- Original HOL4 Theorem: nsSub_compute_thm
-- !R e1 e2. nsSub R e1 e2 ⇔ nsSub_compute [] R e1 e2
theorem nsSub_compute_thm {m n v} [BEq n] [BEq m] (R : id m n → v → v → Prop) (e1 e2 : namespace m n v) :
  nsSub R e1 e2 ↔ nsSub_compute [] R e1 e2 := sorry

-- Original HOL4 Theorem: nsAll2_conj
-- !P Q e1 e2. nsAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2
theorem nsAll2_conj {m n v} [BEq n] [BEq m] (P Q : id m n → v → v → Prop) (e1 e2 : namespace m n v) :
  nsAll2 (fun i x y => P i x y ∧ Q i x y) e1 e2 ↔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 := sorry

-- Original HOL4 Theorem: nsAll2_nsLookup1
-- !R e1 e2 n v1.
    nsLookup e1 n = SOME v1 ∧
    nsAll2 R e1 e2
    ⇒
    ?v2. nsLookup e2 n = SOME v2 ∧ R n v1 v2
theorem nsAll2_nsLookup1 {m n v} [BEq n] [BEq m] (R : id m n → v → v → Prop) (e1 e2 : namespace m n v) (i : id m n) (v1 : v) :
  nsLookup e1 i = some v1 → nsAll2 R e1 e2 → ∃ v2, nsLookup e2 i = some v2 ∧ R i v1 v2 := sorry

-- Original HOL4 Theorem: nsAll2_nsLookup2
-- !R e1 e2 n v2.
    nsLookup e2 n = SOME v2 ∧
    nsAll2 R e1 e2
    ⇒
    ?v1. nsLookup e1 n = SOME v1 ∧ R n v1 v2
theorem nsAll2_nsLookup2 {m n v} [BEq n] [BEq m] (R : id m n → v → v → Prop) (e1 e2 : namespace m n v) (i : id m n) (v2 : v) :
  nsLookup e2 i = some v2 → nsAll2 R e1 e2 → ∃ v1, nsLookup e1 i = some v1 ∧ R i v1 v2 := sorry

-- Original HOL4 Theorem: nsAll2_nsLookup_none
-- !R e1 e2 n.
    nsAll2 R e1 e2
    ⇒
    (nsLookup e1 n = NONE ⇔ nsLookup e2 n = NONE)
theorem nsAll2_nsLookup_none {m n v} [BEq n] [BEq m] (R : id m n → v → v → Prop) (e1 e2 : namespace m n v) (i : id m n) :
  nsAll2 R e1 e2 → (nsLookup e1 i = none ↔ nsLookup e2 i = none) := sorry

-- Original HOL4 Theorem: nsAll2_nsBind
-- !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsAll2 R e1 e2 ⇒ nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2)
theorem nsAll2_nsBind {m n v} [BEq n] [BEq m] (R : id m n → v → v → Prop) (x : n) (v1 v2 : v) (e1 e2 : namespace m n v) :
  R (id.Short x) v1 v2 → nsAll2 R e1 e2 → nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) := sorry

-- Original HOL4 Theorem: nsAll2_nsBindList
-- !R l1 l2 e1 e2.
     LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2
     ⇒
     nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2)
theorem nsAll2_nsBindList {m n v} [BEq n] [BEq m] [DecidableEq n] (R : id m n → v → v → Prop) (l1 l2 : List (n × v)) (e1 e2 : namespace m n v) :
  List.Forall₂ (fun p1 p2 => p1.1 = p2.1 ∧ R (id.Short p1.1) p1.2 p2.2) l1 l2 → nsAll2 R e1 e2 →
  nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := sorry

-- Original HOL4 Theorem: nsAll2_nsAppend
-- !R e1 e1' e2 e2'.
    nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' ⇒ nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2')
theorem nsAll2_nsAppend {m n v} [BEq n] [BEq m] (R : id m n → v → v → Prop) (e1 e1' e2 e2' : namespace m n v) :
  nsAll2 R e1 e2 → nsAll2 R e1' e2' → nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := sorry

-- Original HOL4 Theorem: nsAll2_alist_to_ns
-- !R l1 l2. LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ⇒ nsAll2 R (alist_to_ns l1) (alist_to_ns l2)
theorem nsAll2_alist_to_ns {m n v} [BEq n] [BEq m] [DecidableEq n] (R : id m n → v → v → Prop) (l1 l2 : List (n × v)) :
  List.Forall₂ (fun p1 p2 => p1.1 = p2.1 ∧ R (id.Short p1.1) p1.2 p2.2) l1 l2 →
  nsAll2 R (alist_to_ns l1) (alist_to_ns l2) := sorry

-- Original HOL4 Theorem: nsMap_compose
-- ∀g e f. nsMap f (nsMap g e) = nsMap (f o g) e
theorem nsMap_compose {m n v w u} (g : v → w) (e : namespace m n v) (f : w → u) :
  nsMap f (nsMap g e) = nsMap (f ∘ g) e := sorry

-- Original HOL4 Theorem: nsMap_nsAppend
-- !n1 n2 f. nsMap f (nsAppend n1 n2) = nsAppend (nsMap f n1) (nsMap f n2)
theorem nsMap_nsAppend {m n v w} (n1 n2 : namespace m n v) (f : v → w) :
  nsMap f (nsAppend n1 n2) = nsAppend (nsMap f n1) (nsMap f n2) := sorry

-- Original HOL4 Theorem: nsLookupMod_nsMap
-- !n x f. nsLookupMod (nsMap f n) x = OPTION_MAP (nsMap f) (nsLookupMod n x)
theorem nsLookupMod_nsMap {m n v w} [BEq m] (ns : namespace m n v) (x : List m) (f : v → w) :
  nsLookupMod (nsMap f ns) x = Option.map (nsMap f) (nsLookupMod ns x) := sorry

-- Original HOL4 Theorem: nsLookup_nsMap
-- !n x f. nsLookup (nsMap f n) x = OPTION_MAP f (nsLookup n x)
theorem nsLookup_nsMap {m n v w} [BEq n] [BEq m] (ns : namespace m n v) (x : id m n) (f : v → w) :
  nsLookup (nsMap f ns) x = Option.map f (nsLookup ns x) := sorry

-- Original HOL4 Theorem: nsAll_nsMap
-- !f n P. nsAll P (nsMap f n) ⇔ nsAll (\x y. P x (f y)) n
theorem nsAll_nsMap {m n v w} [BEq n] [BEq m] (f : v → w) (ns : namespace m n v) (P : id m n → w → Prop) :
  nsAll P (nsMap f ns) ↔ nsAll (fun x y => P x (f y)) ns := sorry

-- Original HOL4 Theorem: nsLift_nsMap
-- !f n mn. nsLift mn (nsMap f n) = nsMap f (nsLift mn n)
theorem nsLift_nsMap {m n v w} (f : v → w) (n : namespace m n v) (mn : m) :
  nsLift mn (nsMap f n) = nsMap f (nsLift mn n) := sorry

-- Original HOL4 Theorem: nsSub_nsMap
-- !R f n1 n2.
    nsSub R (nsMap f n1) (nsMap f n2) ⇔ nsSub (\id x y. R id (f x) (f y)) n1 n2
theorem nsSub_nsMap {m n v w} [BEq n] [BEq m] (R : id m n → w → w → Prop) (f : v → w) (n1 n2 : namespace m n v) :
  nsSub R (nsMap f n1) (nsMap f n2) ↔ nsSub (fun id x y => R id (f x) (f y)) n1 n2 := sorry

-- Original HOL4 Theorem: nsLookup_nsDom
-- !x n. x ∈ nsDom n ⇔ ?v. nsLookup n x = SOME v
theorem nsLookup_nsDom {m n v} [BEq n] [BEq m] (x : id m n) (ns : namespace m n v) :
  x ∈ nsDom ns ↔ ∃ v, nsLookup ns x = some v := sorry

-- Original HOL4 Theorem: nsDom_nsAppend_equal
-- !n1 n2 n3 n4.
    nsDom n1 = nsDom n3 ∧
    nsDom n2 = nsDom n4 ∧
    nsDomMod n1 = nsDomMod n3 ∧
    nsDomMod n2 = nsDomMod n4
    ⇒
    nsDom (nsAppend n1 n2) = nsDom (nsAppend n3 n4) ∧
    nsDomMod (nsAppend n1 n2) = nsDomMod (nsAppend n3 n4)
theorem nsDom_nsAppend_equal {m n v} [BEq n] [BEq m] (n1 n2 n3 n4 : namespace m n v) :
  nsDom n1 = nsDom n3 → nsDom n2 = nsDom n4 → nsDomMod n1 = nsDomMod n3 → nsDomMod n2 = nsDomMod n4 →
  nsDom (nsAppend n1 n2) = nsDom (nsAppend n3 n4) ∧
  nsDomMod (nsAppend n1 n2) = nsDomMod (nsAppend n3 n4) := sorry

-- Original HOL4 Theorem: nsDom_nsLift
-- !mn n. nsDom (nsLift mn n) = IMAGE (Long mn) (nsDom n)
theorem nsDom_nsLift {m n v} [BEq n] [BEq m] (mn : m) (ns : namespace m n v) :
  nsDom (nsLift mn ns) = (fun i => id.Long mn i) '' (nsDom ns) := sorry

-- Original HOL4 Theorem: nsDomMod_nsLift
-- !mn n. nsDomMod (nsLift mn n) = [] INSERT IMAGE (CONS mn) (nsDomMod n)
theorem nsDomMod_nsLift {m n v} [BEq m] (mn : m) (ns : namespace m n v) :
  nsDomMod (nsLift mn ns) = insert [] ((fun p => mn :: p) '' (nsDomMod ns)) := sorry

-- Original HOL4 Theorem: nsDom_nsAppend_flat
-- !n1 n2.nsDomMod n1 = {[]} ⇒ nsDom (nsAppend n1 n2) = nsDom n1 ∪ nsDom n2
theorem nsDom_nsAppend_flat {m n v} [BEq n] [BEq m] (n1 n2 : namespace m n v) :
  nsDomMod n1 = {[]} → nsDom (nsAppend n1 n2) = nsDom n1 ∪ nsDom n2 := sorry

-- Original HOL4 Theorem: nsDomMod_nsAppend_flat
-- !n1 n2.nsDomMod n1 = {[]} ⇒ nsDomMod (nsAppend n1 n2) = nsDomMod n2
theorem nsDomMod_nsAppend_flat {m n v} [BEq m] (n1 n2 : namespace m n v) :
  nsDomMod n1 = {[]} → nsDomMod (nsAppend n1 n2) = nsDomMod n2 := sorry

