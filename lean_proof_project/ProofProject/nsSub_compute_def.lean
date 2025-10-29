-- LEAN 4 file for theorem: nsSub_compute_def
-- Original HOL4 Definition

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsSub_compute_def : structure Env (α : Type) where
  var_map : List (String × α)
  ns_map  : List (String × Env α)
def mk_id (path : List String) (name : String) : String :=
  String.intercalate "." ((List.reverse path).append [name])
def List.lookup {k v : Type} [DecidableEq k] (key : k) (l : List (k × v)) : Option v :=
  l.findM (fun (k', v') => if k' == key then some v' else none)
def alistSub {k_type v_type : Type} [DecidableEq k_type] (R_elt : k_type → v_type → v_type → Prop)
    (l1 : List (k_type × v_type)) (l2 : List (k_type × v_type)) : Prop :=
  ∀ (k : k_type) (v1 : v_type),
    (l1.lookup k) = some v1 →
    ∃ (v2 : v_type), (l2.lookup k) = some v2 ∧ R_elt k v1 v2
mutual
  def namespace_size_rec_impl (f_var : String → Nat) (f_ns : String → Nat) (f_val : α → Nat) : Env α → Nat
    | ⟨var_map, ns_map⟩ =>
      var_map.foldl (fun acc (k, v) => acc + f_var k + f_val v) 0 +
      ns_map.foldl (fun acc (k, env) => acc + f_ns k + namespace_size_rec_impl f_var f_ns f_val env) 0
  def namespace_size_rec (f_var : String → Nat) (f_ns : String → Nat) (f_val : α → Nat) (env : Env α) : Nat :=
    namespace_size_rec_impl f_var f_ns f_val env
end
def nsSub_compute (α : Type) [DecidableEq String] (path : List String) (R : String → α → α → Prop)
    (env1 : Env α) (env2 : Env α) : Prop :=
  alistSub (fun k v1 v2 => R (mk_id (List.reverse path) k) v1 v2) env1.var_map env2.var_map ∧
  alistSub (fun k v1_ns v2_ns => nsSub_compute α (k :: path) R v1_ns v2_ns) env1.ns_map env2.ns_map
termination_by nsSub_compute α path R env1 env2 => namespace_size_rec (fun _ => 0) (fun _ => 0) (fun _ => 0) env1 := by
  aesop
