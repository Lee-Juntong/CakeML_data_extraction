-- Auto-generated LEAN 4 file from HOL4 translation
-- Theory: namespace
-- Generated using Gemini API

namespace CML_Lean.namespace

/-
Original HOL4 Type: alist
``: ('k # 'v) list``
-/
-- In HOL4, 'alist' often refers to a list of pairs. In Lean, this is directly represented as 'List (k × v)'.

/-
Original HOL4 Datatype: id
id = Short 'n | Long 'm id
-/
inductive cml_id (n_type m_type : Type) where
  | Short : n_type → cml_id n_type m_type
  | Long  : m_type → cml_id n_type m_type → cml_id n_type m_type
  deriving Repr, DecidableEq

/-
Original HOL4 Definition: mk_id_def
mk_id [] n = Short n ∧
  mk_id (mn::mns) n = Long mn (mk_id mns n)
-/
def mk_cml_id {n_type m_type : Type} : List m_type → n_type → cml_id n_type m_type
  | [], n       => cml_id.Short n
  | mn :: mns, n => cml_id.Long mn (mk_cml_id mns n)

/-
Original HOL4 Definition: id_to_n_def
id_to_n (Short n) = n ∧
 id_to_n (Long _ id) = id_to_n id
-/
def cml_id_to_n {n_type m_type : Type} : cml_id n_type m_type → n_type
  | cml_id.Short n     => n
  | cml_id.Long _ cml_id_tail => cml_id_to_n cml_id_tail

/-
Original HOL4 Definition: id_to_mods_def
id_to_mods (Short _) = [] ∧
  id_to_mods (Long mn id) = mn::id_to_mods id
-/
def cml_id_to_mods {n_type m_type : Type} : cml_id n_type m_type → List m_type
  | cml_id.Short _     => []
  | cml_id.Long mn cml_id_tail => mn :: cml_id_to_mods cml_id_tail

/-
Original HOL4 Datatype: namespace
namespace =
    Bind (('n,'v) alist) (('m,namespace) alist)
-/
inductive cml_namespace (m_type n_type v_type : Type) where
  | Bind : List (n_type × v_type) → List (m_type × cml_namespace m_type n_type v_type) → cml_namespace m_type n_type v_type
  deriving Repr, DecidableEq

/-
Original HOL4 Definition: nsLookup_def
nsLookup ((Bind v m):('m,'n,'v)namespace) (Short n) =
    ALOOKUP v n ∧
  nsLookup (Bind v m) (Long mn id) =
    case ALOOKUP m mn of
    | NONE => NONE
    | SOME env => nsLookup env id
-/
def ns_lookup {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (env : cml_namespace m_type n_type v_type) (cml_id_val : cml_id n_type m_type) : Option v_type :=
  match env, cml_id_val with
  | cml_namespace.Bind v _, cml_id.Short n => alist_lookup v n
  | cml_namespace.Bind _ m, cml_id.Long mn cml_id_tail =>
    match alist_lookup m mn with
    | none      => none
    | some sub_env => ns_lookup sub_env cml_id_tail

/-
Original HOL4 Definition: nsLookupMod_def
nsLookupMod e [] = SOME (e:('m,'n,'v)namespace) ∧
  nsLookupMod (Bind v m) (mn::path) =
  case ALOOKUP m mn of NONE => NONE | SOME env => nsLookupMod env path
-/
def ns_lookup_mod {m_type n_type v_type : Type} [DecidableEq m_type]
  (env : cml_namespace m_type n_type v_type) (path : List m_type) : Option (cml_namespace m_type n_type v_type) :=
  match path with
  | []       => some env
  | mn :: path_tail =>
    match env with
    | cml_namespace.Bind _ m =>
      match alist_lookup m mn with
      | none      => none
      | some sub_env => ns_lookup_mod sub_env path_tail

/-
Original HOL4 Definition: nsEmpty_def
nsEmpty = Bind [] []
-/
def ns_empty {m_type n_type v_type : Type} : cml_namespace m_type n_type v_type :=
  cml_namespace.Bind [] []

/-
Original HOL4 Definition: nsAppend_def
nsAppend (Bind v1 m1) (Bind v2 m2) = Bind (v1 ++ v2) (m1 ++ m2)
-/
def ns_append {m_type n_type v_type : Type}
  (env1 env2 : cml_namespace m_type n_type v_type) : cml_namespace m_type n_type v_type :=
  match env1, env2 with
  | cml_namespace.Bind v1 m1, cml_namespace.Bind v2 m2 =>
    cml_namespace.Bind (v1 ++ v2) (m1 ++ m2)

/-
Original HOL4 Definition: nsLift_def
nsLift mn env = Bind [] [(mn,env)]
-/
def ns_lift {m_type n_type v_type : Type} (mn : m_type) (env : cml_namespace m_type n_type v_type) : cml_namespace m_type n_type v_type :=
  cml_namespace.Bind [] [(mn, env)]

/-
Original HOL4 Definition: alist_to_ns_def
alist_to_ns a = Bind a []
-/
def alist_to_ns {m_type n_type v_type : Type} (a : List (n_type × v_type)) : cml_namespace m_type n_type v_type :=
  cml_namespace.Bind a []

/-
Original HOL4 Definition: nsBind_def
nsBind k x (Bind v m) = Bind ((k,x)::v) m
-/
def ns_bind {m_type n_type v_type : Type} (k : n_type) (x : v_type)
  (env : cml_namespace m_type n_type v_type) : cml_namespace m_type n_type v_type :=
  match env with
  | cml_namespace.Bind v m => cml_namespace.Bind ((k, x) :: v) m

/-
Original HOL4 Definition: nsBindList_def
nsBindList l e = FOLDR (λ(x,v) e. nsBind x v e) e l
-/
def ns_bind_list {m_type n_type v_type : Type} (l : List (n_type × v_type))
  (e : cml_namespace m_type n_type v_type) : cml_namespace m_type n_type v_type :=
  l.foldr (fun (x, v_val) acc_env => ns_bind x v_val acc_env) e

/-
Original HOL4 Definition: nsOptBind_def
nsOptBind n x env = case n of NONE => env | SOME n => nsBind n x env
-/
def ns_opt_bind {m_type n_type v_type : Type} (n_opt : Option n_type) (x : v_type)
  (env : cml_namespace m_type n_type v_type) : cml_namespace m_type n_type v_type :=
  match n_opt with
  | none    => env
  | some n_val => ns_bind n_val x env

/-
Original HOL4 Definition: nsSing_def
nsSing n x = Bind [(n,x)] []
-/
def ns_sing {m_type n_type v_type : Type} (n : n_type) (x : v_type) : cml_namespace m_type n_type v_type :=
  cml_namespace.Bind [(n, x)] []

/-
Original HOL4 Definition: nsSub_def
nsSub r env1 env2 ⇔
     (∀id v1.
        nsLookup env1 id = SOME v1 ⇒
        ∃v2. nsLookup env2 id = SOME v2 ∧ r id v1 v2) ∧
     ∀path. nsLookupMod env2 path = NONE ⇒ nsLookupMod env1 path = NONE
-/
import Mathlib.Data.Set.Basic

def ns_sub {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (r : cml_id n_type m_type → v_type → v_type → Prop)
  (env1 env2 : cml_namespace m_type n_type v_type) : Prop :=
  (∀ cml_id_val : cml_id n_type m_type, ∀ v1 : v_type,
    ns_lookup env1 cml_id_val = some v1 →
    ∃ v2 : v_type, ns_lookup env2 cml_id_val = some v2 ∧ r cml_id_val v1 v2) ∧
  (∀ path : List m_type,
    ns_lookup_mod env2 path = none → ns_lookup_mod env1 path = none)

/-
Original HOL4 Definition: nsAll_def
nsAll f env ⇔ ∀id v. nsLookup env id = SOME v ⇒ f id v
-/
def ns_all {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (f : cml_id n_type m_type → v_type → Prop)
  (env : cml_namespace m_type n_type v_type) : Prop :=
  ∀ cml_id_val : cml_id n_type m_type, ∀ v : v_type,
    ns_lookup env cml_id_val = some v → f cml_id_val v

/-
Original HOL4 Definition: nsAll2_def
nsAll2 r env1 env2 ⇔
    nsSub r env1 env2 ∧ nsSub (λx y z. r x z y) env2 env1
-/
def ns_all2 {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (r : cml_id n_type m_type → v_type → v_type → Prop)
  (env1 env2 : cml_namespace m_type n_type v_type) : Prop :=
  ns_sub r env1 env2 ∧ ns_sub (fun x z y => r x y z) env2 env1

/-
Original HOL4 Definition: nsDom_def
nsDom (env:('m,'n,'v)namespace) =
     {n | (v,n) | v ∈ 𝕌(:φ) ∧ n ∈ 𝕌(:(ν, ξ) id) ∧ nsLookup env n = SOME v}
-/
import Mathlib.Data.Set.Basic

def ns_dom {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (env : cml_namespace m_type n_type v_type) : Set (cml_id n_type m_type) :=
  { k | ∃ v, ns_lookup env k = some v }

/-
Original HOL4 Definition: nsDomMod_def
nsDomMod (env:('m,'n,'v)namespace) =
     {n | (v,n) | v ∈ 𝕌(:(ν, ξ, φ) namespace) ∧ n ∈ 𝕌(:ν list) ∧
                  nsLookupMod env n = SOME v}
-/
import Mathlib.Data.Set.Basic

def ns_dom_mod {m_type n_type v_type : Type} [DecidableEq m_type]
  (env : cml_namespace m_type n_type v_type) : Set (List m_type) :=
  { path | ∃ sub_env, ns_lookup_mod env path = some sub_env }

/-
Original HOL4 Definition: nsMap_def
nsMap (f:'v -> 'w) ((Bind v m):('m,'n,'v)namespace) =
    Bind (MAP (λ(n,x). (n,f x)) v) (MAP (λ(mn,e). (mn,nsMap f e)) m)
-/
def ns_map {m_type n_type v_type w_type : Type}
  (f : v_type → w_type) (env : cml_namespace m_type n_type v_type) : cml_namespace m_type n_type w_type :=
  match env with
  | cml_namespace.Bind v m =>
    cml_namespace.Bind
      (v.map (fun (n_val, x) => (n_val, f x)))
      (m.map (fun (mn, sub_env) => (mn, ns_map f sub_env)))

end CML_Lean.namespace
