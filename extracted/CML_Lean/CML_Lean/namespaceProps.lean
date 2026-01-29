-- Auto-generated LEAN 4 file from HOL4 translation
-- Theory: namespaceProps
-- Generated using Gemini API

-- Import ancestor theories
import CML_Lean.ast
import CML_Lean.namespace

namespace CML_Lean.namespaceProps

/-
Original HOL4 Theorem: mk_id_11
!a b c d. mk_id a b = mk_id c d ⇔ (a = c) ∧ (b = d)
-/
theorem mk_cml_id_injective {n_type m_type : Type} (a c : List m_type) (b d : n_type) :
  mk_cml_id a b = mk_cml_id c d ↔ (a = c ∧ b = d) := by sorry

/-
Original HOL4 Theorem: id_to_mods_mk_id
!mn x. id_to_mods (mk_id mn x) = mn
-/
theorem cml_id_to_mods_mk_cml_id {n_type m_type : Type} (mn : List m_type) (x : n_type) :
  cml_id_to_mods (mk_cml_id mn x) = mn := by sorry

/-
Original HOL4 Theorem: id_to_namemods_mk_id
!mn x. id_to_n (mk_id mn x) = x
-/
theorem cml_id_to_n_mk_cml_id {n_type m_type : Type} (mn : List m_type) (x : n_type) :
  cml_id_to_n (mk_cml_id mn x) = x := by sorry

/-
Original HOL4 Theorem: mk_id_surj
!id. ?p n. id = mk_id p n
-/
theorem mk_cml_id_surjective {n_type m_type : Type} (cml_id_val : cml_id n_type m_type) :
  ∃ (p : List m_type) (n : n_type), cml_id_val = mk_cml_id p n := by sorry

/-
Original HOL4 Theorem: mk_id_thm
!id. mk_id (id_to_mods id) (id_to_n id) = id
-/
theorem mk_cml_id_identity {n_type m_type : Type} (cml_id_val : cml_id n_type m_type) :
  mk_cml_id (cml_id_to_mods cml_id_val) (cml_id_to_n cml_id_val) = cml_id_val := by sorry

/-
Original HOL4 Theorem: nsAll_mono
(!id x. P id x ⇒ Q id x) ⇒ nsAll P e ⇒ nsAll Q e
-/
theorem ns_all_mono {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (P Q : cml_id n_type m_type → v_type → Prop) (e : cml_namespace m_type n_type v_type) :
  (∀ id x, P id x → Q id x) → ns_all P e → ns_all Q e := by sorry

/-
Original HOL4 Theorem: nsSub_mono
(!x y z. R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2)
-/
theorem ns_sub_mono {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R1 R2 : cml_id n_type m_type → v_type → v_type → Prop) (e1 e2 : cml_namespace m_type n_type v_type) :
  (∀ x y z, R1 x y z → R2 x y z) → (ns_sub R1 e1 e2 → ns_sub R2 e1 e2) := by sorry

/-
Original HOL4 Theorem: nsSub_mono2
(!x y z. nsLookup e1 x = SOME y ∧ nsLookup e2 x = SOME z ∧ R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2)
-/
theorem ns_sub_mono2 {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R1 R2 : cml_id n_type m_type → v_type → v_type → Prop) (e1 e2 : cml_namespace m_type n_type v_type) :
  (∀ x y z,
    ns_lookup e1 x = some y ∧ ns_lookup e2 x = some z ∧ R1 x y z → R2 x y z) →
  (ns_sub R1 e1 e2 → ns_sub R2 e1 e2) := by sorry

/-
Original HOL4 Theorem: nsAll2_mono
(!x y z. R1 x y z ⇒ R2 x y z) ⇒ nsAll2 R1 e1 e2 ⇒ nsAll2 R2 e1 e2
-/
theorem ns_all2_mono {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R1 R2 : cml_id n_type m_type → v_type → v_type → Prop) (e1 e2 : cml_namespace m_type n_type v_type) :
  (∀ x y z, R1 x y z → R2 x y z) → ns_all2 R1 e1 e2 → ns_all2 R2 e1 e2 := by sorry

/-
Original HOL4 Theorem: nsLookup_nsEmpty
!id. nsLookup nsEmpty id = NONE
-/
theorem ns_lookup_ns_empty {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type] (cml_id_val : cml_id n_type m_type) :
  ns_lookup (ns_empty : cml_namespace m_type n_type v_type) cml_id_val = none := by sorry

/-
Original HOL4 Theorem: nsLookupMod_nsEmpty
!x y. nsLookupMod nsEmpty (x::y) = NONE
-/
theorem ns_lookup_mod_ns_empty {m_type n_type v_type : Type} [DecidableEq m_type] (x : m_type) (y : List m_type) :
  ns_lookup_mod (ns_empty : cml_namespace m_type n_type v_type) (x :: y) = none := by sorry

/-
Original HOL4 Theorem: nsAppend_nsEmpty
!env. nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env
-/
theorem ns_append_ns_empty {m_type n_type v_type : Type} (env : cml_namespace m_type n_type v_type) :
  ns_append env ns_empty = env ∧ ns_append ns_empty env = env := by sorry

/-
Original HOL4 Theorem: alist_to_ns_nil
alist_to_ns [] = nsEmpty
-/
theorem alist_to_ns_nil {m_type n_type v_type : Type} :
  alist_to_ns ([] : List (n_type × v_type)) = (ns_empty : cml_namespace m_type n_type v_type) := by sorry

/-
Original HOL4 Theorem: nsSub_nsEmpty
!r env. nsSub r nsEmpty env
-/
theorem ns_sub_ns_empty {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (r : cml_id n_type m_type → v_type → v_type → Prop) (env : cml_namespace m_type n_type v_type) :
  ns_sub r (ns_empty : cml_namespace m_type n_type v_type) env := by sorry

/-
Original HOL4 Theorem: nsAll_nsEmpty
!f. nsAll f nsEmpty
-/
theorem ns_all_ns_empty {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (f : cml_id n_type m_type → v_type → Prop) :
  ns_all f (ns_empty : cml_namespace m_type n_type v_type) := by sorry

/-
Original HOL4 Theorem: nsAll2_nsEmpty
!f. nsAll2 f nsEmpty nsEmpty
-/
theorem ns_all2_ns_empty {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (f : cml_id n_type m_type → v_type → v_type → Prop) :
  ns_all2 f (ns_empty : cml_namespace m_type n_type v_type) (ns_empty : cml_namespace m_type n_type v_type) := by sorry

/-
Original HOL4 Theorem: nsDom_nsEmpty
nsDom nsEmpty = {}
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_ns_empty {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type] :
  ns_dom (ns_empty : cml_namespace m_type n_type v_type) = (∅ : Set (cml_id n_type m_type)) := by sorry

/-
Original HOL4 Theorem: nsDomMod_nsEmpty
nsDomMod nsEmpty = {[]}
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_mod_ns_empty {m_type n_type v_type : Type} [DecidableEq m_type] :
  ns_dom_mod (ns_empty : cml_namespace m_type n_type v_type) = ({[]} : Set (List m_type)) := by sorry

/-
Original HOL4 Theorem: nsMap_nsEmpty
!f. nsMap f nsEmpty = nsEmpty
-/
theorem ns_map_ns_empty {m_type n_type v_type w_type : Type} (f : v_type → w_type) :
  ns_map f (ns_empty : cml_namespace m_type n_type v_type) = (ns_empty : cml_namespace m_type n_type w_type) := by sorry

/-
Original HOL4 Theorem: nsBind_nsEmpty
!x y env. nsBind x y env ≠ nsEmpty
-/
theorem ns_bind_ns_empty_ne {m_type n_type v_type : Type} (x : n_type) (y : v_type) (env : cml_namespace m_type n_type v_type) :
  ns_bind x y env ≠ (ns_empty : cml_namespace m_type n_type v_type) := by sorry

/-
Original HOL4 Theorem: nsLookup_Bind_v_some
nsLookup (Bind v []) k = SOME x ⇔
   ∃y. k = Short y ∧ ALOOKUP v y = SOME x
-/
theorem ns_lookup_bind_v_some {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (v : List (n_type × v_type)) (k : cml_id n_type m_type) (x : v_type) :
  ns_lookup (cml_namespace.Bind v []) k = some x ↔
  (∃ y : n_type, k = cml_id.Short y ∧ alist_lookup v y = some x) := by sorry

/-
Original HOL4 Theorem: alist_to_ns_cons
!k v l. alist_to_ns ((k,v)::l) = nsBind k v (alist_to_ns l)
-/
theorem alist_to_ns_cons {m_type n_type v_type : Type} (k : n_type) (v_val : v_type) (l : List (n_type × v_type)) :
  alist_to_ns ((k, v_val) :: l) = ns_bind k v_val (alist_to_ns l) := by sorry

/-
Original HOL4 Theorem: nsAppend_nsBind
!k v e1 e2. nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2)
-/
theorem ns_append_ns_bind {m_type n_type v_type : Type} (k : n_type) (v_val : v_type) (e1 e2 : cml_namespace m_type n_type v_type) :
  ns_append (ns_bind k v_val e1) e2 = ns_bind k v_val (ns_append e1 e2) := by sorry

/-
Original HOL4 Theorem: nsAppend_alist_to_ns
!al1 al2. nsAppend (alist_to_ns al1) (alist_to_ns al2) = alist_to_ns (al1 ++ al2)
-/
theorem ns_append_alist_to_ns {m_type n_type v_type : Type} (al1 al2 : List (n_type × v_type)) :
  ns_append (alist_to_ns al1) (alist_to_ns al2) = alist_to_ns (al1 ++ al2) := by sorry

/-
Original HOL4 Theorem: nsAppend_assoc
!e1 e2 e3. nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3
-/
theorem ns_append_assoc {m_type n_type v_type : Type} (e1 e2 e3 : cml_namespace m_type n_type v_type) :
  ns_append e1 (ns_append e2 e3) = ns_append (ns_append e1 e2) e3 := by sorry

/-
Original HOL4 Theorem: nsLookup_nsBind
(!n v e. nsLookup (nsBind n v e) (Short n) = SOME v) ∧
   (!n n' v e. n ≠ Short n' ⇒ nsLookup (nsBind n' v e) n = nsLookup e n)
-/
theorem ns_lookup_ns_bind {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (n : n_type) (v_val : v_type) (e : cml_namespace m_type n_type v_type) :
  ns_lookup (ns_bind n v_val e) (cml_id.Short n) = some v_val ∧
  (∀ (n' : cml_id n_type m_type), n' ≠ cml_id.Short n → ns_lookup (ns_bind n v_val e) n' = ns_lookup e n') := by sorry

/-
Original HOL4 Theorem: nsAppend_nsSing
!n x e. nsAppend (nsSing n x) e = nsBind n x e
-/
theorem ns_append_ns_sing {m_type n_type v_type : Type} (n : n_type) (x : v_type) (e : cml_namespace m_type n_type v_type) :
  ns_append (ns_sing n x) e = ns_bind n x e := by sorry

/-
Original HOL4 Theorem: nsLookup_nsSing
!n v id. nsLookup (nsSing n v) id = if id = Short n then SOME v else NONE
-/
theorem ns_lookup_ns_sing {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (n : n_type) (v_val : v_type) (cml_id_val : cml_id n_type m_type) :
  ns_lookup (ns_sing n v_val) cml_id_val = if cml_id_val = cml_id.Short n then some v_val else none := by sorry

/-
Original HOL4 Theorem: nsAll_nsSing
!R n v. nsAll R (nsSing n v) ⇔ R (Short n) v
-/
theorem ns_all_ns_sing {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → Prop) (n : n_type) (v_val : v_type) :
  ns_all R (ns_sing n v_val) ↔ R (cml_id.Short n) v_val := by sorry

/-
Original HOL4 Theorem: nsAll2_nsSing
!R n1 v1 n2 v2. nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ⇔ n1 = n2 ∧ R (Short n1) v1 v2
-/
theorem ns_all2_ns_sing {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (n1 : n_type) (v1 : v_type) (n2 : n_type) (v2 : v_type) :
  ns_all2 R (ns_sing n1 v1) (ns_sing n2 v2) ↔ n1 = n2 ∧ R (cml_id.Short n1) v1 v2 := by sorry

/-
Original HOL4 Theorem: nsMap_nsSing
!f x v. nsMap f (nsSing x v) = nsSing x (f v)
-/
theorem ns_map_ns_sing {m_type n_type v_type w_type : Type} (f : v_type → w_type) (x : n_type) (v_val : v_type) :
  ns_map f (ns_sing x v_val) = ns_sing x (f v_val) := by sorry

/-
Original HOL4 Theorem: nsLookupMod_nsSing
!n1 n2 v. nsLookupMod (nsSing n2 v) n1 = if n1 = [] then SOME (nsSing n2 v) else NONE
-/
theorem ns_lookup_mod_ns_sing {m_type n_type v_type : Type} [DecidableEq m_type]
  (n1 : List m_type) (n2 : n_type) (v_val : v_type) :
  ns_lookup_mod (ns_sing n2 v_val) n1 = if n1 = [] then some (ns_sing n2 v_val) else none := by sorry

/-
Original HOL4 Theorem: nsBind_11
!x y n x' y' n'. nsBind x y n = nsBind x' y' n' ⇔ x = x' ∧ y = y' ∧ n = n'
-/
theorem ns_bind_injective {m_type n_type v_type : Type}
  (x x' : n_type) (y y' : v_type) (n n' : cml_namespace m_type n_type v_type) :
  ns_bind x y n = ns_bind x' y' n' ↔ x = x' ∧ y = y' ∧ n = n' := by sorry

/-
Original HOL4 Theorem: nsDom_nsBind
!x y n. nsDom (nsBind x y n) = Short x INSERT nsDom n
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_ns_bind {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (x : n_type) (y : v_type) (n_val : cml_namespace m_type n_type v_type) :
  ns_dom (ns_bind x y n_val) = ({cml_id.Short x} : Set (cml_id n_type m_type)) ∪ ns_dom n_val := by sorry

/-
Original HOL4 Theorem: nsDom_nsSing
!x y. nsDom (nsSing x y) = {Short x}
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_ns_sing {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (x : n_type) (y : v_type) :
  ns_dom (ns_sing x y) = ({cml_id.Short x} : Set (cml_id n_type m_type)) := by sorry

/-
Original HOL4 Theorem: nsDomMod_nsBind
!x y n. nsDomMod (nsBind x y n) = nsDomMod n
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_mod_ns_bind {m_type n_type v_type : Type} [DecidableEq m_type]
  (x : n_type) (y : v_type) (n_val : cml_namespace m_type n_type v_type) :
  ns_dom_mod (ns_bind x y n_val) = ns_dom_mod n_val := by sorry

/-
Original HOL4 Theorem: nsDomMod_nsSing
!x y. nsDomMod (nsSing x y) = {[]}
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_mod_ns_sing {m_type n_type v_type : Type} [DecidableEq m_type]
  (x : n_type) (y : v_type) :
  ns_dom_mod (ns_sing x y) = ({[]} : Set (List m_type)) := by sorry

/-
Original HOL4 Theorem: nsLookupMod_alist_to_ns
!l x y. nsLookupMod (alist_to_ns l) (x::y) = NONE
-/
theorem ns_lookup_mod_alist_to_ns {m_type n_type v_type : Type} [DecidableEq m_type]
  (l : List (n_type × v_type)) (x : m_type) (y : List m_type) :
  ns_lookup_mod (alist_to_ns l) (x :: y) = none := by sorry

/-
Original HOL4 Theorem: alist_to_ns_11
!l1 l2. alist_to_ns l1 = alist_to_ns l2 ⇔ l1 = l2
-/
theorem alist_to_ns_injective {m_type n_type v_type : Type} (l1 l2 : List (n_type × v_type)) :
  alist_to_ns l1 = alist_to_ns l2 ↔ l1 = l2 := by sorry

/-
Original HOL4 Theorem: nsLookup_to_nsLookupMod
!n v t.
    nsLookup n v = SOME t
    ⇒
    ?m. nsLookupMod n (id_to_mods v) = SOME m ∧ nsLookup m (Short (id_to_n v)) = SOME t
-/
theorem ns_lookup_to_ns_lookup_mod {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (n_env : cml_namespace m_type n_type v_type) (v_id : cml_id n_type m_type) (t : v_type) :
  ns_lookup n_env v_id = some t →
  (∃ m_env : cml_namespace m_type n_type v_type,
    ns_lookup_mod n_env (cml_id_to_mods v_id) = some m_env ∧
    ns_lookup m_env (cml_id.Short (cml_id_to_n v_id)) = some t) := by sorry

/-
Original HOL4 Theorem: nsLookup_alist_to_ns_some
!l id v. nsLookup (alist_to_ns l) id = SOME v ⇔ ?x'. id = Short x' ∧ ALOOKUP l x' = SOME v
-/
theorem ns_lookup_alist_to_ns_some {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (l : List (n_type × v_type)) (cml_id_val : cml_id n_type m_type) (v_val : v_type) :
  ns_lookup (alist_to_ns l) cml_id_val = some v_val ↔
  (∃ x' : n_type, cml_id_val = cml_id.Short x' ∧ alist_lookup l x' = some v_val) := by sorry

/-
Original HOL4 Theorem: nsLookup_alist_to_ns_none
!l id. nsLookup (alist_to_ns l) id = NONE ⇔ !x'. id = Short x' ⇒ ALOOKUP l x' = NONE
-/
theorem ns_lookup_alist_to_ns_none {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (l : List (n_type × v_type)) (cml_id_val : cml_id n_type m_type) :
  ns_lookup (alist_to_ns l) cml_id_val = none ↔
  (∀ x' : n_type, cml_id_val = cml_id.Short x' → alist_lookup l x' = none) := by sorry

/-
Original HOL4 Theorem: nsDom_alist_to_ns
!l. nsDom (alist_to_ns l) = set (MAP (Short o FST) l)
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_alist_to_ns {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (l : List (n_type × v_type)) :
  ns_dom (alist_to_ns l) = (l.map (fun (k, _) => cml_id.Short k)).toSet := by sorry

/-
Original HOL4 Theorem: nsLookup_nsLift
!mn e id.
    nsLookup (nsLift mn e) id =
    case id of
    | Long mn' id' =>
      if mn = mn' then
        nsLookup e id'
      else
        NONE
    | Short _ => NONE
-/
theorem ns_lookup_ns_lift {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (mn : m_type) (e : cml_namespace m_type n_type v_type) (cml_id_val : cml_id n_type m_type) :
  ns_lookup (ns_lift mn e) cml_id_val =
  (match cml_id_val with
  | cml_id.Long mn' id' =>
    if mn = mn' then
      ns_lookup e id'
    else
      none
  | cml_id.Short _ => none) := by sorry

/-
Original HOL4 Theorem: nsLookupMod_nsLift
!mn e path.
    nsLookupMod (nsLift mn e) path =
    case path of
    | [] => SOME (nsLift mn e)
    | (mn'::path') =>
      if mn = mn' then
        nsLookupMod e path'
      else
        NONE
-/
theorem ns_lookup_mod_ns_lift {m_type n_type v_type : Type} [DecidableEq m_type]
  (mn : m_type) (e : cml_namespace m_type n_type v_type) (path : List m_type) :
  ns_lookup_mod (ns_lift mn e) path =
  (match path with
  | []       => some (ns_lift mn e)
  | mn' :: path' =>
    if mn = mn' then
      ns_lookup_mod e path'
    else
      none) := by sorry

/-
Original HOL4 Theorem: nsLookup_nsLift_append
!m ns ns' m' id n.
   nsLookup (nsAppend (nsLift m ns) ns') (Short n) = nsLookup ns' (Short n) ∧
   nsLookup (nsAppend (nsLift m ns) ns') (Long m' id) =
     if m = m' then nsLookup ns id else nsLookup ns' (Long m' id)
-/
theorem ns_lookup_ns_lift_append {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (m : m_type) (ns ns' : cml_namespace m_type n_type v_type) (m' : m_type) (cml_id_val : cml_id n_type m_type) (n_val : n_type) :
  ns_lookup (ns_append (ns_lift m ns) ns') (cml_id.Short n_val) = ns_lookup ns' (cml_id.Short n_val) ∧
  ns_lookup (ns_append (ns_lift m ns) ns') (cml_id.Long m' cml_id_val) =
    (if m = m' then ns_lookup ns cml_id_val else ns_lookup ns' (cml_id.Long m' cml_id_val)) := by sorry

/-
Original HOL4 Theorem: nsLookup_nsAppend_none
∀e1 id e2.
    nsLookup (nsAppend e1 e2) id = NONE
    ⇔
    (nsLookup e1 id = NONE ∧
     (nsLookup e2 id = NONE ∨
      ?p1 p2 e3. p1 ≠ [] ∧ id_to_mods id = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3))
-/
theorem ns_lookup_ns_append_none {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (e1 id e2 : cml_namespace m_type n_type v_type) :
  ns_lookup (ns_append e1 e2) id = none ↔
  (ns_lookup e1 id = none ∧
   (ns_lookup e2 id = none ∨
    ∃ (p1 : List m_type) (p2 : List m_type) (e3 : cml_namespace m_type n_type v_type),
      p1 ≠ [] ∧ cml_id_to_mods id = p1 ++ p2 ∧ ns_lookup_mod e1 p1 = some e3)) := by sorry

/-
Original HOL4 Theorem: nsLookup_nsAppend_some
∀e1 id e2 v.
    nsLookup (nsAppend e1 e2) id = SOME v
    ⇔
    nsLookup e1 id = SOME v ∨
    (nsLookup e1 id = NONE ∧ nsLookup e2 id = SOME v ∧
     !p1 p2. p1 ≠ [] ∧ id_to_mods id = p1++p2 ⇒ nsLookupMod e1 p1 = NONE)
-/
theorem ns_lookup_ns_append_some {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (e1 id e2 : cml_namespace m_type n_type v_type) (v : v_type) :
  ns_lookup (ns_append e1 e2) id = some v ↔
  ns_lookup e1 id = some v ∨
  (ns_lookup e1 id = none ∧ ns_lookup e2 id = some v ∧
   (∀ (p1 p2 : List m_type),
     p1 ≠ [] ∧ cml_id_to_mods id = p1 ++ p2 → ns_lookup_mod e1 p1 = none)) := by sorry

/-
Original HOL4 Theorem: nsAppend_to_nsBindList
!l. nsAppend (alist_to_ns l) e = nsBindList l e
-/
theorem ns_append_to_ns_bind_list {m_type n_type v_type : Type} (l : List (n_type × v_type)) (e : cml_namespace m_type n_type v_type) :
  ns_append (alist_to_ns l) e = ns_bind_list l e := by sorry

/-
Original HOL4 Theorem: nsLookupMod_nsAppend_none
!e1 e2 path.
    nsLookupMod (nsAppend e1 e2) path = NONE
    ⇔
    (nsLookupMod e1 path = NONE ∧
     (nsLookupMod e2 path = NONE ∨
      ?p1 p2 e3. p1 ≠ [] ∧ path = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3))
-/
import Std.Data.List.Basic

theorem ns_lookup_mod_ns_append_none {m_type n_type v_type : Type} [DecidableEq m_type]
  (e1 e2 : cml_namespace m_type n_type v_type) (path : List m_type) :
  ns_lookup_mod (ns_append e1 e2) path = none ↔
  (ns_lookup_mod e1 path = none ∧
   (ns_lookup_mod e2 path = none ∨
    ∃ (p1 p2 : List m_type) (e3 : cml_namespace m_type n_type v_type),
      p1 ≠ [] ∧ path = p1 ++ p2 ∧ ns_lookup_mod e1 p1 = some e3)) := by sorry

/-
Original HOL4 Theorem: nsLookupMod_nsAppend_some
!e1 e2 path.
    (nsLookupMod (nsAppend e1 e2) path = SOME x
     ⇔
     if path = [] then x = nsAppend e1 e2 else
     nsLookupMod e1 path = SOME x ∨
      (nsLookupMod e2 path = SOME x ∧
      !p1 p2. p1 ≠ [] ∧ path = p1++p2 ⇒ nsLookupMod e1 p1 = NONE))
-/
import Std.Data.List.Basic

theorem ns_lookup_mod_ns_append_some {m_type n_type v_type : Type} [DecidableEq m_type]
  (e1 e2 : cml_namespace m_type n_type v_type) (path : List m_type) (x : cml_namespace m_type n_type v_type) :
  (ns_lookup_mod (ns_append e1 e2) path = some x ↔
   (path = [] ∧ x = ns_append e1 e2) ∨
   (ns_lookup_mod e1 path = some x ∨
    (ns_lookup_mod e2 path = some x ∧
     (∀ (p1 p2 : List m_type),
       p1 ≠ [] ∧ path = p1 ++ p2 → ns_lookup_mod e1 p1 = none)))) := by sorry

/-
Original HOL4 Theorem: nsDom_nsAppend_alist
!x y. nsDom (nsAppend (alist_to_ns x) y) = set (MAP (Short o FST) x) ∪ nsDom y
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_ns_append_alist {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (x : List (n_type × v_type)) (y : cml_namespace m_type n_type v_type) :
  ns_dom (ns_append (alist_to_ns x) y) = (x.map (fun (k,_) => cml_id.Short k)).toSet ∪ ns_dom y := by sorry

/-
Original HOL4 Theorem: eALL_T
!e. nsAll (\n x. T) e
-/
theorem ns_all_True {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (e : cml_namespace m_type n_type v_type) :
  ns_all (fun (_ : cml_id n_type m_type) (_ : v_type) => True) e := by sorry

/-
Original HOL4 Theorem: nsLookup_nsAll
!env x P v. nsAll P env ∧ nsLookup env x = SOME v ⇒ P x v
-/
theorem ns_lookup_ns_all {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (env : cml_namespace m_type n_type v_type) (x : cml_id n_type m_type) (P : cml_id n_type m_type → v_type → Prop) (v : v_type) :
  ns_all P env ∧ ns_lookup env x = some v → P x v := by sorry

/-
Original HOL4 Theorem: nsAll_nsAppend
!f e1 e2. nsAll f e1 ∧ nsAll f e2 ⇒ nsAll f (nsAppend e1 e2)
-/
theorem ns_all_ns_append {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (f : cml_id n_type m_type → v_type → Prop) (e1 e2 : cml_namespace m_type n_type v_type) :
  ns_all f e1 ∧ ns_all f e2 → ns_all f (ns_append e1 e2) := by sorry

/-
Original HOL4 Theorem: nsAll_nsBind
!P x v e. P (Short x) v ∧ nsAll P e ⇒ nsAll P (nsBind x v e)
-/
theorem ns_all_ns_bind {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (P : cml_id n_type m_type → v_type → Prop) (x : n_type) (v : v_type) (e : cml_namespace m_type n_type v_type) :
  P (cml_id.Short x) v ∧ ns_all P e → ns_all P (ns_bind x v e) := by sorry

/-
Original HOL4 Theorem: nsAll_nsOptBind
!P x v e. (x = NONE ∨ ?n. x = SOME n ∧ P (Short n) v) ∧ nsAll P e ⇒ nsAll P (nsOptBind x v e)
-/
theorem ns_all_ns_opt_bind {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (P : cml_id n_type m_type → v_type → Prop) (x : Option n_type) (v : v_type) (e : cml_namespace m_type n_type v_type) :
  (x = none ∨ (∃ n_val : n_type, x = some n_val ∧ P (cml_id.Short n_val) v)) ∧ ns_all P e → ns_all P (ns_opt_bind x v e) := by sorry

/-
Original HOL4 Theorem: nsAll_alist_to_ns
!R l. EVERY (λ(n,v). R (Short n) v) l ⇒ nsAll R (alist_to_ns l)
-/
theorem ns_all_alist_to_ns {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → Prop) (l : List (n_type × v_type)) :
  (l.Forall (fun (n_val, v_val) => R (cml_id.Short n_val) v_val)) → ns_all R (alist_to_ns l) := by sorry

/-
Original HOL4 Theorem: nsAll_nsLift
!R mn e. nsAll R (nsLift mn e) ⇔ nsAll (\id. R (Long mn id)) e
-/
theorem ns_all_ns_lift {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → Prop) (mn : m_type) (e : cml_namespace m_type n_type v_type) :
  ns_all R (ns_lift mn e) ↔ ns_all (fun (id : cml_id n_type m_type) => R (cml_id.Long mn id)) e := by sorry

/-
Original HOL4 Theorem: nsAll_nsAppend_left
!P n1 n2. nsAll P (nsAppend n1 n2) ⇒ nsAll P n1
-/
theorem ns_all_ns_append_left {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (P : cml_id n_type m_type → v_type → Prop) (n1 n2 : cml_namespace m_type n_type v_type) :
  ns_all P (ns_append n1 n2) → ns_all P n1 := by sorry

/-
Original HOL4 Theorem: nsSub_conj
!P Q e1 e2. nsSub (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsSub P e1 e2 ∧
  nsSub Q e1 e2
-/
theorem ns_sub_conj {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (P Q : cml_id n_type m_type → v_type → v_type → Prop) (e1 e2 : cml_namespace m_type n_type v_type) :
  ns_sub (fun id x y => P id x y ∧ Q id x y) e1 e2 ↔ ns_sub P e1 e2 ∧ ns_sub Q e1 e2 := by sorry

/-
Original HOL4 Theorem: nsSub_refl
!P R. (!n x. P n x ⇒ R n x x) ⇒ !e. nsAll P e ⇒ nsSub R e e
-/
theorem ns_sub_refl {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (P : cml_id n_type m_type → v_type → Prop) (R : cml_id n_type m_type → v_type → v_type → Prop) :
  (∀ n x, P n x → R n x x) → (∀ e : cml_namespace m_type n_type v_type, ns_all P e → ns_sub R e e) := by sorry

/-
Original HOL4 Theorem: nsSub_nsBind
!R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsSub R e1 e2 ⇒ nsSub R (nsBind x v1 e1) (nsBind x v2 e2)
-/
theorem ns_sub_ns_bind {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop) (x : n_type) (v1 v2 : v_type) (e1 e2 : cml_namespace m_type n_type v_type) :
  R (cml_id.Short x) v1 v2 ∧ ns_sub R e1 e2 → ns_sub R (ns_bind x v1 e1) (ns_bind x v2 e2) := by sorry

/-
Original HOL4 Theorem: nsSub_nsAppend2
!R e1 e2 e2'. nsSub R e1 e1 ∧ nsSub R e2 e2' ⇒ nsSub R (nsAppend e1 e2) (nsAppend e1 e2')
-/
theorem ns_sub_ns_append2 {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop) (e1 e2 e2' : cml_namespace m_type n_type v_type) :
  (∀ id v, ns_lookup e1 id = some v → R id v v) ∧ ns_sub R e2 e2' → ns_sub R (ns_append e1 e2) (ns_append e1 e2') := by sorry

/-
Original HOL4 Theorem: nsSub_nsAppend_lift
!R mn e1 e1' e2 e2'.
    nsSub (\id. R (Long mn id)) e1 e1' ∧
    nsSub R e2 e2'
    ⇒
    nsSub R (nsAppend (nsLift mn e1) e2) (nsAppend (nsLift mn e1') e2')
-/
theorem ns_sub_ns_append_lift {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop) (mn : m_type)
  (e1 e1' e2 e2' : cml_namespace m_type n_type v_type) :
  ns_sub (fun id => R (cml_id.Long mn id)) e1 e1' ∧
  ns_sub R e2 e2' →
  ns_sub R (ns_append (ns_lift mn e1) e2) (ns_append (ns_lift mn e1') e2') := by sorry

/-
Original HOL4 Definition: alist_rel_restr_def
(alist_rel_restr R l1 l2 [] ⇔ T) ∧
  (alist_rel_restr R l1 l2 (k1::keys) ⇔
    case ALOOKUP l1 k1 of
    | NONE => F
    | SOME v1 =>
      case ALOOKUP l2 k1 of
      | NONE => F
      | SOME v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys)
-/
def alist_rel_restr {k v : Type} [DecidableEq k]
  (R : k → v → v → Prop) (l1 l2 : List (k × v)) (keys : List k) : Prop :=
  match keys with
  | []       => True
  | k1 :: ks =>
    (match alist_lookup l1 k1, alist_lookup l2 k1 with
    | some v1, some v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 ks
    | _, _             => False)

/-
Original HOL4 Theorem: alist_rel_restr_thm
!R e1 e2 keys.
    alist_rel_restr R e1 e2 keys ⇔
      !k. MEM k keys ⇒ ?v1 v2. ALOOKUP e1 k = SOME v1 ∧ ALOOKUP e2 k = SOME v2 ∧ R k v1 v2
-/
theorem alist_rel_restr_thm {k v : Type} [DecidableEq k]
  (R : k → v → v → Prop) (e1 e2 : List (k × v)) (keys : List k) :
  alist_rel_restr R e1 e2 keys ↔
  (∀ k_val : k, k_val ∈ keys → ∃ v1 v2, alist_lookup e1 k_val = some v1 ∧ alist_lookup e2 k_val = some v2 ∧ R k_val v1 v2) := by sorry

/-
Original HOL4 Definition: alistSub_def
alistSub R e1 e2 ⇔ alist_rel_restr R e1 e2 (MAP FST e1)
-/
def alist_sub {k v : Type} [DecidableEq k]
  (R : k → v → v → Prop) (e1 e2 : List (k × v)) : Prop :=
  alist_rel_restr R e1 e2 (e1.map Prod.fst)

/-
Original HOL4 Theorem: alistSub_cong
!l1 l2 l1' l2' R R'.
    l1 = l1' ∧ l2 = l2' ∧ (!n x y. ALOOKUP l1' n = SOME x ∧ ALOOKUP l2' n = SOME y ⇒ R n x y = R' n x y) ⇒
    (alistSub R l1 l2 ⇔ alistSub R' l1' l2')
-/
theorem alist_sub_cong {k v : Type} [DecidableEq k]
  (l1 l2 l1' l2' : List (k × v)) (R R' : k → v → v → Prop) :
  l1 = l1' ∧ l2 = l2' ∧
  (∀ n x y, alist_lookup l1' n = some x ∧ alist_lookup l2' n = some y → R n x y = R' n x y) →
  (alist_sub R l1 l2 ↔ alist_sub R' l1' l2') := by sorry

/-
Original HOL4 Definition: nsSub_compute_def
nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ⇔
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
-/
import Std.Data.List.Basic

def ns_sub_compute {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (path : List m_type)
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (env1 env2 : cml_namespace m_type n_type v_type) : Prop :=
  match env1, env2 with
  | cml_namespace.Bind e1V e1M, cml_namespace.Bind e2V e2M =>
    alist_sub (fun k v1 v2 => R (mk_cml_id (List.reverse path) k) v1 v2) e1V e2V ∧
    alist_sub (fun k v1 v2 => ns_sub_compute (k :: path) R v1 v2) e1M e2M
termination_by
  ns_sub_compute path R env1 env2 => sizeOf env1

/-
Original HOL4 Theorem: nsLookup_FOLDR_nsLift
!e p k. nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Short k)
-/
theorem ns_lookup_foldr_ns_lift {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (e : cml_namespace m_type n_type v_type) (p : List m_type) (k : n_type) :
  ns_lookup (List.foldr (ns_lift) e p) (mk_cml_id p k) = ns_lookup e (cml_id.Short k) := by sorry

/-
Original HOL4 Theorem: nsLookup_FOLDR_nsLift_some
!e p id v.
    nsLookup (FOLDR nsLift e p) id = SOME v ⇔
    (p = [] ∧ nsLookup e id = SOME v) ∨
    (p ≠ [] ∧ ?p2 n. id = mk_id (p++p2) n ∧ nsLookup e (mk_id p2 n) = SOME v)
-/
theorem ns_lookup_foldr_ns_lift_some {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (e : cml_namespace m_type n_type v_type) (p : List m_type) (id : cml_id n_type m_type) (v : v_type) :
  ns_lookup (List.foldr (ns_lift) e p) id = some v ↔
  (p = [] ∧ ns_lookup e id = some v) ∨
  (p ≠ [] ∧ ∃ (p2 : List m_type) (n_val : n_type),
    id = mk_cml_id (p ++ p2) n_val ∧ ns_lookup e (mk_cml_id p2 n_val) = some v) := by sorry

/-
Original HOL4 Theorem: nsLookupMod_FOLDR_nsLift_none
!e p1 p2. nsLookupMod (FOLDR nsLift e p1) p2 = NONE ⇔
    (IS_PREFIX p1 p2 ∨ IS_PREFIX p2 p1) ⇒
    ?p3. p2 = p1++p3 ∧ nsLookupMod e p3 = NONE
-/
import Std.Data.List.Basic

theorem ns_lookup_mod_foldr_ns_lift_none {m_type n_type v_type : Type} [DecidableEq m_type]
  (e : cml_namespace m_type n_type v_type) (p1 p2 : List m_type) :
  ns_lookup_mod (List.foldr (ns_lift) e p1) p2 = none ↔
  ((p1.isPrefix p2 ∨ p2.isPrefix p1) →
  (∃ (p3 : List m_type), p2 = p1 ++ p3 ∧ ns_lookup_mod e p3 = none)) := by sorry

/-
Original HOL4 Theorem: nsSub_compute_thm_general
!p R e1 e2.
    nsSub R (FOLDR nsLift e1 (REVERSE p)) (FOLDR nsLift e2 (REVERSE p)) ⇔
    nsSub_compute p R e1 e2
-/
import Std.Data.List.Basic

theorem ns_sub_compute_thm_general {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (p : List m_type) (R : cml_id n_type m_type → v_type → v_type → Prop)
  (e1 e2 : cml_namespace m_type n_type v_type) :
  ns_sub R (List.foldr (ns_lift) e1 (List.reverse p)) (List.foldr (ns_lift) e2 (List.reverse p)) ↔
  ns_sub_compute p R e1 e2 := by sorry

/-
Original HOL4 Theorem: nsSub_compute_thm
!R e1 e2. nsSub R e1 e2 ⇔ nsSub_compute [] R e1 e2
-/
theorem ns_sub_compute_thm {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (e1 e2 : cml_namespace m_type n_type v_type) :
  ns_sub R e1 e2 ↔ ns_sub_compute [] R e1 e2 := by sorry

/-
Original HOL4 Theorem: nsAll2_conj
!P Q e1 e2. nsAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2
-/
theorem ns_all2_conj {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (P Q : cml_id n_type m_type → v_type → v_type → Prop)
  (e1 e2 : cml_namespace m_type n_type v_type) :
  ns_all2 (fun id x y => P id x y ∧ Q id x y) e1 e2 ↔ ns_all2 P e1 e2 ∧ ns_all2 Q e1 e2 := by sorry

/-
Original HOL4 Theorem: nsAll2_nsLookup1
!R e1 e2 n v1.
    nsLookup e1 n = SOME v1 ∧
    nsAll2 R e1 e2
    ⇒
    ?v2. nsLookup e2 n = SOME v2 ∧ R n v1 v2
-/
theorem ns_all2_ns_lookup1 {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (e1 e2 : cml_namespace m_type n_type v_type) (n : cml_id n_type m_type) (v1 : v_type) :
  ns_lookup e1 n = some v1 ∧ ns_all2 R e1 e2 →
  (∃ v2 : v_type, ns_lookup e2 n = some v2 ∧ R n v1 v2) := by sorry

/-
Original HOL4 Theorem: nsAll2_nsLookup2
!R e1 e2 n v2.
    nsLookup e2 n = SOME v2 ∧
    nsAll2 R e1 e2
    ⇒
    ?v1. nsLookup e1 n = SOME v1 ∧ R n v1 v2
-/
theorem ns_all2_ns_lookup2 {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (e1 e2 : cml_namespace m_type n_type v_type) (n : cml_id n_type m_type) (v2 : v_type) :
  ns_lookup e2 n = some v2 ∧ ns_all2 R e1 e2 →
  (∃ v1 : v_type, ns_lookup e1 n = some v1 ∧ R n v1 v2) := by sorry

/-
Original HOL4 Theorem: nsAll2_nsLookup_none
!R e1 e2 n.
    nsAll2 R e1 e2
    ⇒
    (nsLookup e1 n = NONE ⇔ nsLookup e2 n = NONE)
-/
theorem ns_all2_ns_lookup_none {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (e1 e2 : cml_namespace m_type n_type v_type) (n : cml_id n_type m_type) :
  ns_all2 R e1 e2 → (ns_lookup e1 n = none ↔ ns_lookup e2 n = none) := by sorry

/-
Original HOL4 Theorem: nsAll2_nsBind
!R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsAll2 R e1 e2 ⇒ nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2)
-/
theorem ns_all2_ns_bind {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (x : n_type) (v1 v2 : v_type) (e1 e2 : cml_namespace m_type n_type v_type) :
  R (cml_id.Short x) v1 v2 ∧ ns_all2 R e1 e2 → ns_all2 R (ns_bind x v1 e1) (ns_bind x v2 e2) := by sorry

/-
Original HOL4 Theorem: nsAll2_nsBindList
!R l1 l2 e1 e2.
     LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2
     ⇒
     nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2)
-/
theorem ns_all2_ns_bind_list {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (l1 l2 : List (n_type × v_type)) (e1 e2 : cml_namespace m_type n_type v_type) :
  (List.Forall₂ (fun (kv1 : n_type × v_type) (kv2 : n_type × v_type) =>
    kv1.fst = kv2.fst ∧ R (cml_id.Short kv1.fst) kv1.snd kv2.snd) l1 l2) ∧
  ns_all2 R e1 e2 →
  ns_all2 R (ns_bind_list l1 e1) (ns_bind_list l2 e2) := by sorry

/-
Original HOL4 Theorem: nsAll2_nsAppend
!R e1 e1' e2 e2'.
    nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' ⇒ nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2')
-/
theorem ns_all2_ns_append {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (e1 e1' e2 e2' : cml_namespace m_type n_type v_type) :
  ns_all2 R e1 e2 ∧ ns_all2 R e1' e2' → ns_all2 R (ns_append e1 e1') (ns_append e2 e2') := by sorry

/-
Original HOL4 Theorem: nsAll2_alist_to_ns
!R l1 l2. LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ⇒ nsAll2 R (alist_to_ns l1) (alist_to_ns l2)
-/
theorem ns_all2_alist_to_ns {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (l1 l2 : List (n_type × v_type)) :
  (List.Forall₂ (fun (kv1 : n_type × v_type) (kv2 : n_type × v_type) =>
    kv1.fst = kv2.fst ∧ R (cml_id.Short kv1.fst) kv1.snd kv2.snd) l1 l2) →
  ns_all2 R (alist_to_ns l1) (alist_to_ns l2) := by sorry

/-
Original HOL4 Theorem: nsAll2_nsLift
!R mn e1 e2. nsAll2 R (nsLift mn e1) (nsLift mn e2) ⇔ nsAll2 (\id. R (Long mn id)) e1 e2
-/
theorem ns_all2_ns_lift {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → v_type → v_type → Prop)
  (mn : m_type) (e1 e2 : cml_namespace m_type n_type v_type) :
  ns_all2 R (ns_lift mn e1) (ns_lift mn e2) ↔ ns_all2 (fun id x y => R (cml_id.Long mn id) x y) e1 e2 := by sorry

/-
Original HOL4 Theorem: nsMap_alist_to_ns
!f l. nsMap f (alist_to_ns l) = alist_to_ns (MAP (\(k,v). (k, f v)) l)
-/
theorem ns_map_alist_to_ns {m_type n_type v_type w_type : Type} (f : v_type → w_type) (l : List (n_type × v_type)) :
  ns_map f (alist_to_ns l) = alist_to_ns (l.map (fun (k, v_val) => (k, f v_val))) := by sorry

/-
Original HOL4 Theorem: nsMap_compose
∀g e f. nsMap f (nsMap g e) = nsMap (f o g) e
-/
theorem ns_map_compose {m_type n_type v_type w_type x_type : Type}
  (g : v_type → w_type) (e : cml_namespace m_type n_type v_type) (f : w_type → x_type) :
  ns_map f (ns_map g e) = ns_map (f ∘ g) e := by sorry

/-
Original HOL4 Theorem: nsMap_I
∀ns. nsMap I ns = ns
-/
theorem ns_map_id {m_type n_type v_type : Type}
  (ns : cml_namespace m_type n_type v_type) :
  ns_map id ns = ns := by sorry

/-
Original HOL4 Theorem: nsMap_nsAppend
!n1 n2 f. nsMap f (nsAppend n1 n2) = nsAppend (nsMap f n1) (nsMap f n2)
-/
theorem ns_map_ns_append {m_type n_type v_type w_type : Type}
  (n1 n2 : cml_namespace m_type n_type v_type) (f : v_type → w_type) :
  ns_map f (ns_append n1 n2) = ns_append (ns_map f n1) (ns_map f n2) := by sorry

/-
Original HOL4 Theorem: nsLookupMod_nsMap
!n x f. nsLookupMod (nsMap f n) x = OPTION_MAP (nsMap f) (nsLookupMod n x)
-/
theorem ns_lookup_mod_ns_map {m_type n_type v_type w_type : Type} [DecidableEq m_type]
  (n : cml_namespace m_type n_type v_type) (x : List m_type) (f : v_type → w_type) :
  ns_lookup_mod (ns_map f n) x = Option.map (ns_map f) (ns_lookup_mod n x) := by sorry

/-
Original HOL4 Theorem: nsLookup_nsMap
!n x f. nsLookup (nsMap f n) x = OPTION_MAP f (nsLookup n x)
-/
theorem ns_lookup_ns_map {m_type n_type v_type w_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (n : cml_namespace m_type n_type v_type) (x : cml_id n_type m_type) (f : v_type → w_type) :
  ns_lookup (ns_map f n) x = Option.map f (ns_lookup n x) := by sorry

/-
Original HOL4 Theorem: nsAll_nsMap
!f n P. nsAll P (nsMap f n) ⇔ nsAll (\x y. P x (f y)) n
-/
theorem ns_all_ns_map {m_type n_type v_type w_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (f : v_type → w_type) (n : cml_namespace m_type n_type v_type) (P : cml_id n_type m_type → w_type → Prop) :
  ns_all P (ns_map f n) ↔ ns_all (fun x y => P x (f y)) n := by sorry

/-
Original HOL4 Theorem: nsLift_nsMap
!f n mn. nsLift mn (nsMap f n) = nsMap f (nsLift mn n)
-/
theorem ns_lift_ns_map {m_type n_type v_type w_type : Type}
  (f : v_type → w_type) (n : cml_namespace m_type n_type v_type) (mn : m_type) :
  ns_lift mn (ns_map f n) = ns_map f (ns_lift mn n) := by sorry

/-
Original HOL4 Theorem: nsSub_nsMap
!R f n1 n2.
    nsSub R (nsMap f n1) (nsMap f n2) ⇔ nsSub (\id x y. R id (f x) (f y)) n1 n2
-/
theorem ns_sub_ns_map {m_type n_type v_type w_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (R : cml_id n_type m_type → w_type → w_type → Prop) (f : v_type → w_type)
  (n1 n2 : cml_namespace m_type n_type v_type) :
  ns_sub R (ns_map f n1) (ns_map f n2) ↔ ns_sub (fun id x y => R id (f x) (f y)) n1 n2 := by sorry

/-
Original HOL4 Theorem: nsLookup_nsDom
!x n. x ∈ nsDom n ⇔ ?v. nsLookup n x = SOME v
-/
import Mathlib.Data.Set.Basic

theorem ns_lookup_ns_dom {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (x : cml_id n_type m_type) (n : cml_namespace m_type n_type v_type) :
  x ∈ ns_dom n ↔ (∃ v, ns_lookup n x = some v) := by sorry

/-
Original HOL4 Theorem: nsDomMod_alist_to_ns
!l. nsDomMod (alist_to_ns l) = {[]}
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_mod_alist_to_ns {m_type n_type v_type : Type} [DecidableEq m_type]
  (l : List (n_type × v_type)) :
  ns_dom_mod (alist_to_ns l) = ({[]} : Set (List m_type)) := by sorry

/-
Original HOL4 Theorem: nsDom_nsAppend_equal
!n1 n2 n3 n4.
    nsDom n1 = nsDom n3 ∧
    nsDom n2 = nsDom n4 ∧
    nsDomMod n1 = nsDomMod n3 ∧
    nsDomMod n2 = nsDomMod n4
    ⇒
    nsDom (nsAppend n1 n2) = nsDom (nsAppend n3 n4) ∧
    nsDomMod (nsAppend n1 n2) = nsDomMod (nsAppend n3 n4)
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_ns_append_equal {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (n1 n2 n3 n4 : cml_namespace m_type n_type v_type) :
  ns_dom n1 = ns_dom n3 ∧
  ns_dom n2 = ns_dom n4 ∧
  ns_dom_mod n1 = ns_dom_mod n3 ∧
  ns_dom_mod n2 = ns_dom_mod n4 →
  ns_dom (ns_append n1 n2) = ns_dom (ns_append n3 n4) ∧
  ns_dom_mod (ns_append n1 n2) = ns_dom_mod (ns_append n3 n4) := by sorry

/-
Original HOL4 Theorem: nsDom_nsLift
!mn n. nsDom (nsLift mn n) = IMAGE (Long mn) (nsDom n)
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_ns_lift {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (mn : m_type) (n : cml_namespace m_type n_type v_type) :
  ns_dom (ns_lift mn n) = Set.image (cml_id.Long mn) (ns_dom n) := by sorry

/-
Original HOL4 Theorem: nsDomMod_nsLift
!mn n. nsDomMod (nsLift mn n) = [] INSERT IMAGE (CONS mn) (nsDomMod n)
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_mod_ns_lift {m_type n_type v_type : Type} [DecidableEq m_type]
  (mn : m_type) (n : cml_namespace m_type n_type v_type) :
  ns_dom_mod (ns_lift mn n) = Set.insert [] (Set.image (List.cons mn) (ns_dom_mod n)) := by sorry

/-
Original HOL4 Theorem: nsDom_nsAppend_flat
!n1 n2.nsDomMod n1 = {[]} ⇒ nsDom (nsAppend n1 n2) = nsDom n1 ∪ nsDom n2
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_ns_append_flat {m_type n_type v_type : Type} [DecidableEq n_type] [DecidableEq m_type]
  (n1 n2 : cml_namespace m_type n_type v_type) :
  ns_dom_mod n1 = ({[]} : Set (List m_type)) → ns_dom (ns_append n1 n2) = ns_dom n1 ∪ ns_dom n2 := by sorry

/-
Original HOL4 Theorem: nsDomMod_nsAppend_flat
!n1 n2.nsDomMod n1 = {[]} ⇒ nsDomMod (nsAppend n1 n2) = nsDomMod n2
-/
import Mathlib.Data.Set.Basic

theorem ns_dom_mod_ns_append_flat {m_type n_type v_type : Type} [DecidableEq m_type]
  (n1 n2 : cml_namespace m_type n_type v_type) :
  ns_dom_mod n1 = ({[]} : Set (List m_type)) → ns_dom_mod (ns_append n1 n2) = ns_dom_mod n2 := by sorry

end CML_Lean.namespaceProps
