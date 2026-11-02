/-
  Translation of primTypesScript.sml and primSemEnvScript.sml
  The primitive types that are in scope before any CakeML program starts, and
  the proof that the primitive semantic environment satisfies the type
  soundness invariant.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Location
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.Evaluate
import LeanTypeSound.TypeSystem
import LeanTypeSound.TypeSoundInvariants
import LeanTypeSound.NamespaceProps

open HOL4

-- ============================================================
-- locationScript.sml (needed by prim_types_program)
-- ============================================================

/- HOL4:
Overload unknown_locn[local] = “UNKNOWNpt”

Definition unknown_loc_def:
  unknown_loc = Locs unknown_locn unknown_locn
End
-/
def unknown_loc : locs := .Locs .UNKNOWNpt .UNKNOWNpt

-- ============================================================
-- primTypesScript.sml
-- ============================================================

/- HOL4:
(* The ordering in the following is important. The stamps generated from the
   exceptions and types must match those in semanticPrimitives *)
Definition prim_types_program_def:
  prim_types_program =
   [Dexn unknown_loc «Bind» [];
    Dexn unknown_loc «Chr» [];
    Dexn unknown_loc «Div» [];
    Dexn unknown_loc «Subscript» [];
    Dtype unknown_loc [([],«bool»,[(«False»,[]); («True»,[])])];
    Dtype unknown_loc
          [([«'a»],«list»,
            [(«[]»,[]); («::»,[Atvar «'a»; Atapp [Atvar «'a»] (Short «list»)])])]]
End
-/
def prim_types_program : List dec :=
  [.Dexn unknown_loc (mlstring.strlit "Bind") [],
   .Dexn unknown_loc (mlstring.strlit "Chr") [],
   .Dexn unknown_loc (mlstring.strlit "Div") [],
   .Dexn unknown_loc (mlstring.strlit "Subscript") [],
   .Dtype unknown_loc [([], mlstring.strlit "bool",
      [(mlstring.strlit "False", []), (mlstring.strlit "True", [])])],
   .Dtype unknown_loc
      [([mlstring.strlit "'a"], mlstring.strlit "list",
        [(mlstring.strlit "[]", []),
         (mlstring.strlit "::",
          [.Atvar (mlstring.strlit "'a"),
           .Atapp [.Atvar (mlstring.strlit "'a")] (.Short (mlstring.strlit "list"))])])]]

/- HOL4:
Definition add_to_sem_env_def:
  add_to_sem_env (st:'ffi state,env) prog =
  case evaluate_decs st env prog of
    (st,Rval env') => SOME (st,extend_dec_env env' env)
  | (st,Rerr _) => NONE
End
-/
def add_to_sem_env {ffi : Type} : cml_state ffi × sem_env → List dec →
    Option (cml_state ffi × sem_env)
  | (st, env), prog =>
    match evaluate_decs st env prog with
    | (st, .Rval env') => some (st, extend_dec_env env' env)
    | (_, .Rerr _) => none

/- HOL4:
Definition prim_sem_env_def:
  prim_sem_env (ffi:'ffi ffi_state) =
  add_to_sem_env
  (<|clock := 0; ffi := ffi; refs := []; next_type_stamp := 0;
     next_exn_stamp := 0; eval_state := NONE;
   |>,
   <|v := nsEmpty; c := nsEmpty|>) prim_types_program
End
-/
def prim_sem_env {ffi : Type} (ffi0 : ffi_state ffi) : Option (cml_state ffi × sem_env) :=
  add_to_sem_env
    ({ clock := 0, ffi := ffi0, refs := [], next_type_stamp := 0,
       next_exn_stamp := 0, eval_state_field := none },
     .mk nsEmpty nsEmpty) prim_types_program

/- HOL4:
Definition prim_tenv_def:
  prim_tenv =
     <|c :=
         alist_to_ns
           (REVERSE
              [(«Bind»,[],[],Texn_num); («Chr»,[],[],Texn_num);
               («Div»,[],[],Texn_num); («Subscript»,[],[],Texn_num);
               («False»,[],[],Tbool_num); («True»,[],[],Tbool_num);
               («[]»,[«'a»],[],Tlist_num);
               («::»,[«'a»],[Tvar «'a»; Tlist (Tvar «'a»)],Tlist_num)]);
       v := nsEmpty;
       t :=
         alist_to_ns
           (REVERSE
              [(«array»,[«'a»],Tapp [Tvar «'a»] Tarray_num);
               («bool»,[],Tapp [] Tbool_num);
               («char»,[],Tapp [] Tchar_num);
               («double»,[],Tapp [] Tdouble_num);
               («exn»,[],Tapp [] Texn_num);
               («int»,[],Tapp [] Tint_num);
               (* Tfn is ->, specially handled *)
               («list»,[«'a»],Tapp [Tvar «'a»] Tlist_num);
               («ref»,[«'a»],Tapp [Tvar «'a»] Tref_num);
               («string»,[],Tapp [] Tstring_num);
               («unit»,[],Tapp [] Ttup_num);
               (* pairs are specially handled *)
               («vector»,[«'a»],Tapp [Tvar «'a»] Tvector_num);
               («word64»,[],Tapp [] Tword64_num);
               («word8»,[],Tapp [] Tword8_num);
               («word8array»,[],Tapp [] Tword8array_num)])|>
End
-/
def prim_tenv : type_env :=
  { c := alist_to_ns
      (List.reverse
        [(mlstring.strlit "Bind", ([], [], Texn_num)),
         (mlstring.strlit "Chr", ([], [], Texn_num)),
         (mlstring.strlit "Div", ([], [], Texn_num)),
         (mlstring.strlit "Subscript", ([], [], Texn_num)),
         (mlstring.strlit "False", ([], [], Tbool_num)),
         (mlstring.strlit "True", ([], [], Tbool_num)),
         (mlstring.strlit "[]", ([mlstring.strlit "'a"], [], Tlist_num)),
         (mlstring.strlit "::", ([mlstring.strlit "'a"],
            [.Tvar (mlstring.strlit "'a"), Tlist (.Tvar (mlstring.strlit "'a"))], Tlist_num))]),
    v := nsEmpty,
    t := alist_to_ns
      (List.reverse
        [(mlstring.strlit "array", ([mlstring.strlit "'a"], .Tapp [.Tvar (mlstring.strlit "'a")] Tarray_num)),
         (mlstring.strlit "bool", ([], .Tapp [] Tbool_num)),
         (mlstring.strlit "char", ([], .Tapp [] Tchar_num)),
         (mlstring.strlit "double", ([], .Tapp [] Tdouble_num)),
         (mlstring.strlit "exn", ([], .Tapp [] Texn_num)),
         (mlstring.strlit "int", ([], .Tapp [] Tint_num)),
         -- Tfn is ->, specially handled
         (mlstring.strlit "list", ([mlstring.strlit "'a"], .Tapp [.Tvar (mlstring.strlit "'a")] Tlist_num)),
         (mlstring.strlit "ref", ([mlstring.strlit "'a"], .Tapp [.Tvar (mlstring.strlit "'a")] Tref_num)),
         (mlstring.strlit "string", ([], .Tapp [] Tstring_num)),
         (mlstring.strlit "unit", ([], .Tapp [] Ttup_num)),
         -- pairs are specially handled
         (mlstring.strlit "vector", ([mlstring.strlit "'a"], .Tapp [.Tvar (mlstring.strlit "'a")] Tvector_num)),
         (mlstring.strlit "word64", ([], .Tapp [] Tword64_num)),
         (mlstring.strlit "word8", ([], .Tapp [] Tword8_num)),
         (mlstring.strlit "word8array", ([], .Tapp [] Tword8array_num))]) }

/- HOL4:
Definition prim_type_ids_def:
  prim_type_ids = set (Tlist_num::Tbool_num::prim_type_nums)
End
-/
def prim_type_ids : Set type_ident :=
  fun x => x ∈ (Tlist_num :: Tbool_num :: prim_type_nums)

-- ============================================================
-- primSemEnvScript.sml
-- ============================================================

-- Auxiliary lemmas for `prim_type_sound_invariants`: computing the primitive
-- semantic environment and checking each part of the invariant.

theorem ev_dexn {ffi : Type} (st : cml_state ffi) (env : sem_env) l cn ts :
    evaluate_decs st env [.Dexn l cn ts] =
    ({ st with next_exn_stamp := st.next_exn_stamp + 1 },
     .Rval (.mk nsEmpty (nsSing cn (ts.length, .ExnStamp st.next_exn_stamp)))) := by
  rw [evaluate_decs]

theorem ev_dtype {ffi : Type} (st : cml_state ffi) (env : sem_env) l tds
    (h : tds.all check_dup_ctors = true) :
    evaluate_decs st env [.Dtype l tds] =
      ({ st with next_type_stamp := st.next_type_stamp + tds.length },
       .Rval (.mk nsEmpty (build_tdefs st.next_type_stamp tds))) := by
  rw [evaluate_decs]; simp [h]

theorem ev_cons {ffi : Type} (st st1 : cml_state ffi) (env env1 : sem_env) d1 d2 ds
    (h : evaluate_decs st env [d1] = (st1, .Rval env1)) (hc : st1.clock = st.clock) :
    evaluate_decs st env (d1 :: d2 :: ds) =
      ((evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds)).1,
        combine_dec_result env1 (evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds)).2) := by
  rw [evaluate_decs]
  have : fix_clock st (evaluate_decs st env [d1]) = (st1, .Rval env1) := by
    rw [h]; cases st1; simp_all [fix_clock]
  split
  · rename_i st1' env1' hh
    rw [this] at hh; cases hh; rfl
  · rename_i hh; rw [this] at hh; cases hh

theorem ev_cons_dexn {ffi : Type} (st : cml_state ffi) (env : sem_env) l cn ts d2 ds :
    evaluate_decs st env (.Dexn l cn ts :: d2 :: ds) =
      ((evaluate_decs { st with next_exn_stamp := st.next_exn_stamp + 1 }
          (extend_dec_env (.mk nsEmpty (nsSing cn (ts.length, .ExnStamp st.next_exn_stamp))) env)
          (d2 :: ds)).1,
        combine_dec_result (.mk nsEmpty (nsSing cn (ts.length, .ExnStamp st.next_exn_stamp)))
          (evaluate_decs { st with next_exn_stamp := st.next_exn_stamp + 1 }
          (extend_dec_env (.mk nsEmpty (nsSing cn (ts.length, .ExnStamp st.next_exn_stamp))) env)
          (d2 :: ds)).2) :=
  ev_cons _ _ _ _ _ _ _ (ev_dexn _ _ _ _ _) rfl

theorem ev_cons_dtype {ffi : Type} (st : cml_state ffi) (env : sem_env) l tds d2 ds
    (h : tds.all check_dup_ctors = true) :
    evaluate_decs st env (.Dtype l tds :: d2 :: ds) =
      ((evaluate_decs { st with next_type_stamp := st.next_type_stamp + tds.length }
          (extend_dec_env (.mk nsEmpty (build_tdefs st.next_type_stamp tds)) env)
          (d2 :: ds)).1,
        combine_dec_result (.mk nsEmpty (build_tdefs st.next_type_stamp tds))
          (evaluate_decs { st with next_type_stamp := st.next_type_stamp + tds.length }
          (extend_dec_env (.mk nsEmpty (build_tdefs st.next_type_stamp tds)) env)
          (d2 :: ds)).2) :=
  ev_cons _ _ _ _ _ _ _ (ev_dtype _ _ _ _ h) rfl

def prim_ctor_env : «namespace» modN conN (Nat × stamp) :=
  .Bind [(mlstring.strlit "::", (2, .TypeStamp (mlstring.strlit "::") 1)),
         (mlstring.strlit "[]", (0, .TypeStamp (mlstring.strlit "[]") 1)),
         (mlstring.strlit "True", (0, .TypeStamp (mlstring.strlit "True") 0)),
         (mlstring.strlit "False", (0, .TypeStamp (mlstring.strlit "False") 0)),
         (mlstring.strlit "Subscript", (0, .ExnStamp 3)),
         (mlstring.strlit "Div", (0, .ExnStamp 2)),
         (mlstring.strlit "Chr", (0, .ExnStamp 1)),
         (mlstring.strlit "Bind", (0, .ExnStamp 0))] []

def prim_st {ffi : Type} (ffi0 : ffi_state ffi) : cml_state ffi :=
  { clock := 0, ffi := ffi0, refs := [], next_type_stamp := 2, next_exn_stamp := 4, eval_state_field := none }

theorem prim_sem_env_eq {ffi : Type} (ffi0 : ffi_state ffi) :
    prim_sem_env ffi0 =
      some (prim_st ffi0, .mk nsEmpty prim_ctor_env) := by
  simp only [prim_sem_env, add_to_sem_env, prim_types_program]
  rw [ev_cons_dexn, ev_cons_dexn, ev_cons_dexn, ev_cons_dexn, ev_cons_dtype _ _ _ _ _ _ (by decide),
    ev_dtype _ _ _ _ (by decide)]
  rfl

def prim_ctMap_list : List (stamp × (List tvarN × List sem_t × type_ident)) :=
  [(.ExnStamp 0, ([], [], Texn_num)),
   (.ExnStamp 2, ([], [], Texn_num)),
   (.ExnStamp 1, ([], [], Texn_num)),
   (.ExnStamp 3, ([], [], Texn_num)),
   (.TypeStamp (mlstring.strlit "[]") 1, ([mlstring.strlit "'a"], [], Tlist_num)),
   (.TypeStamp (mlstring.strlit "::") 1, ([mlstring.strlit "'a"],
      [.Tvar (mlstring.strlit "'a"), Tlist (.Tvar (mlstring.strlit "'a"))], Tlist_num)),
   (.TypeStamp (mlstring.strlit "True") 0, ([], [], Tbool_num)),
   (.TypeStamp (mlstring.strlit "False") 0, ([], [], Tbool_num))]

def prim_ctMap : ctMap := Finmap.alist_to_fmap prim_ctMap_list

theorem alist_to_fmap_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {v : β} :
    Finmap.alist_to_fmap l k = some v → (k, v) ∈ l := by
  unfold Finmap.alist_to_fmap
  cases h : l.find? (fun p => k == p.1) with
  | none => simp
  | some p =>
    intro e
    simp only [Option.map_some, Option.some.injEq] at e
    have hm := List.mem_of_find?_eq_some h
    have hk := List.find?_some h
    simp only [beq_iff_eq] at hk
    subst hk e
    exact hm

theorem prim_ctMap_mem {k v} (h : Finmap.FLOOKUP prim_ctMap k = some v) : (k, v) ∈ prim_ctMap_list :=
  alist_to_fmap_mem h

theorem nsLookup_flat_mem {α : Type} {l : List (conN × α)} {id_ : cml_id modN conN} {v : α} :
    nsLookup («namespace».Bind l [] : «namespace» modN conN α) id_ = some v → (∃ k, id_ = .Short k ∧ (k, v) ∈ l) := by
  cases id_ with
  | Short x => intro h; exact ⟨x, rfl, ALOOKUP_mem (by simpa [nsLookup] using h)⟩
  | Long mn i => simp [nsLookup, ALOOKUP]

theorem nsLookupMod_flat {α : Type} {l : List (conN × α)} {path : List modN} :
    nsLookupMod («namespace».Bind l [] : «namespace» modN conN α) path = none ↔ path ≠ [] := by
  cases path <;> simp [nsLookupMod, ALOOKUP]

theorem prim_tenv_c : prim_tenv.c = «namespace».Bind
    [(mlstring.strlit "::", ([mlstring.strlit "'a"],
            [.Tvar (mlstring.strlit "'a"), Tlist (.Tvar (mlstring.strlit "'a"))], Tlist_num)),
     (mlstring.strlit "[]", ([mlstring.strlit "'a"], [], Tlist_num)),
     (mlstring.strlit "True", ([], [], Tbool_num)),
     (mlstring.strlit "False", ([], [], Tbool_num)),
     (mlstring.strlit "Subscript", ([], [], Texn_num)),
     (mlstring.strlit "Div", ([], [], Texn_num)),
     (mlstring.strlit "Chr", ([], [], Texn_num)),
     (mlstring.strlit "Bind", ([], [], Texn_num))] [] := rfl

theorem prim_tenv_t_flat : ∃ l, prim_tenv.t = «namespace».Bind l [] ∧
    ∀ p ∈ l, check_freevars 0 p.2.1 p.2.2 = true :=
  ⟨_, rfl, by simp [check_freevars]⟩

theorem prim_tenv_ok : tenv_ok prim_tenv := by
  refine ⟨?_, ?_, ?_⟩
  · intro id_ v h
    cases id_ <;> simp [prim_tenv, nsEmpty, nsLookup, ALOOKUP] at h
  · intro id_ v h
    rw [prim_tenv_c] at h
    obtain ⟨k, -, hm⟩ := nsLookup_flat_mem h
    have key : ∀ p ∈ [(mlstring.strlit "::", ([mlstring.strlit "'a"],
            [sem_t.Tvar (mlstring.strlit "'a"), Tlist (.Tvar (mlstring.strlit "'a"))], Tlist_num)),
     (mlstring.strlit "[]", ([mlstring.strlit "'a"], ([] : List sem_t), Tlist_num)),
     (mlstring.strlit "True", ([], [], Tbool_num)),
     (mlstring.strlit "False", ([], [], Tbool_num)),
     (mlstring.strlit "Subscript", ([], [], Texn_num)),
     (mlstring.strlit "Div", ([], [], Texn_num)),
     (mlstring.strlit "Chr", ([], [], Texn_num)),
     (mlstring.strlit "Bind", ([], [], Texn_num))],
        EVERY (check_freevars 0 p.2.1) p.2.2.1 = true := by
      simp [EVERY, check_freevars, Tlist]
    exact key _ hm
  · obtain ⟨l, hl, hok⟩ := prim_tenv_t_flat
    intro id_ v h
    rw [hl] at h
    obtain ⟨k, -, hm⟩ := nsLookup_flat_mem h
    exact hok _ hm

theorem prim_ctMap_ok : ctMap_ok prim_ctMap := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k v h
    have hm := prim_ctMap_mem h
    have key : ∀ p ∈ prim_ctMap_list, EVERY (check_freevars 0 p.2.1) p.2.2.1 = true := by
      simp [prim_ctMap_list, EVERY, check_freevars, Tlist]
    exact key _ hm
  · intro ex tvs ts ti h
    have hm := prim_ctMap_mem h
    simp only [prim_ctMap_list, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq,
      reduceCtorEq, false_and] at hm
    rcases hm with ⟨-, rfl, -, rfl⟩ | ⟨-, rfl, -, rfl⟩ | ⟨-, rfl, -, rfl⟩ | ⟨-, rfl, -, rfl⟩ <;>
      exact ⟨rfl, rfl⟩
  · intro cn x tvs ts ti h
    have hm := prim_ctMap_mem h
    have key : ∀ p ∈ prim_ctMap_list, (match p.1 with
        | .TypeStamp _ _ => !(prim_type_nums.elem p.2.2.2)
        | _ => true) = true := by decide
    have := key _ hm
    simpa using this
  · rintro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨h1, h2⟩
    have key : ∀ p ∈ prim_ctMap_list, ∀ q ∈ prim_ctMap_list,
        p.2.2.2 = q.2.2.2 → same_type p.1 q.1 = true := by decide
    exact key _ (prim_ctMap_mem h1) _ (prim_ctMap_mem h2) rfl

theorem prim_ctMap_none {k : stamp} (h : ∀ p ∈ prim_ctMap_list, k ≠ p.1) :
    Finmap.FLOOKUP prim_ctMap k = none := by
  cases e : Finmap.FLOOKUP prim_ctMap k with
  | none => rfl
  | some v => exact absurd rfl (h _ (prim_ctMap_mem e))

theorem prim_good_ctMap : good_ctMap prim_ctMap := by
  refine ⟨prim_ctMap_ok, ⟨rfl, rfl, ?_⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, ?_⟩⟩
  · rintro cn ⟨h1, h2⟩
    apply prim_ctMap_none
    simp [prim_ctMap_list, bool_type_num, h1, h2]
  · rintro cn ⟨h1, h2⟩
    apply prim_ctMap_none
    simp [prim_ctMap_list, list_type_num, h1, h2]

theorem prim_ctMap_range {x : type_ident}
    (h : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) prim_ctMap) x) :
    x = Texn_num ∨ x = Tlist_num ∨ x = Tbool_num := by
  obtain ⟨a, ha⟩ := h
  simp only [Finmap.o_f] at ha
  cases e : prim_ctMap a with
  | none => rw [e] at ha; cases ha
  | some v =>
    rw [e] at ha
    simp only [Option.map_some, Option.some.injEq] at ha
    subst ha
    have key : ∀ p ∈ prim_ctMap_list,
        (p.2.2.2 == Texn_num || p.2.2.2 == Tlist_num || p.2.2.2 == Tbool_num) = true := by decide
    have := key _ (prim_ctMap_mem (k := a) e)
    simpa [or_assoc] using this

theorem prim_consistent_ctMap {ffi : Type} (ffi0 : ffi_state ffi) (type_ids : Set type_ident)
    (hdisj : DISJOINT type_ids (Set.insert Tlist_num (Set.insert Tbool_num {Texn_num}))) :
    consistent_ctMap (prim_st ffi0) type_ids prim_ctMap := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨h1, h2⟩
    apply hdisj x
    refine ⟨h1, ?_⟩
    rcases prim_ctMap_range h2 with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro cn id_
    have key : ∀ p ∈ prim_ctMap_list, (match p.1 with
        | .TypeStamp _ n => decide (n < 2)
        | .ExnStamp n => decide (n < 4)) = true := by decide
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
      simpa using key _ (prim_ctMap_mem (k := .TypeStamp cn id_) hv)
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
      simpa using key _ (prim_ctMap_mem (k := .ExnStamp id_) hv)

theorem prim_type_all_env :
    type_all_env prim_ctMap Finmap.FEMPTY (.mk nsEmpty prim_ctor_env) prim_tenv := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  · intro id_ v1 h
    change nsLookup prim_ctor_env id_ = some v1 at h
    obtain ⟨k, rfl, hm⟩ := nsLookup_flat_mem h
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, rfl, rfl, rfl⟩
  · intro path h
    rw [prim_tenv_c, nsLookupMod_flat] at h
    exact nsLookupMod_flat.2 h
  · intro id_ v1 h
    rw [prim_tenv_c] at h
    obtain ⟨k, rfl, hm⟩ := nsLookup_flat_mem h
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, rfl, rfl, rfl⟩
  · intro path h
    change nsLookupMod prim_ctor_env path = none at h
    rw [prim_tenv_c]
    exact nsLookupMod_flat.2 (nsLookupMod_flat.1 h)
  · intro id_ v1 h
    change nsLookup («namespace».Bind [] [] : «namespace» modN varN v) id_ = some v1 at h
    cases id_ <;> simp [nsLookup, ALOOKUP] at h
  · intro path h
    exact nsLookupMod_flat.2 (nsLookupMod_flat.1 h)
  · intro id_ v1 h
    cases id_ <;> simp [prim_tenv, nsEmpty, nsLookup, ALOOKUP] at h
  · intro path h
    exact nsLookupMod_flat.2 (nsLookupMod_flat.1 h)

theorem prim_type_s {ffi : Type} (ffi0 : ffi_state ffi) :
    type_s prim_ctMap (prim_st ffi0).refs Finmap.FEMPTY := by
  intro l
  simp [prim_st, Finmap.FLOOKUP, Finmap.FEMPTY, store_lookup]

/- HOL4 (not translated): `Theorem prim_sem_env_eq = EVAL ``prim_sem_env (ffi:'ffi ffi_state)```
   is a derived rule application whose statement is whatever EVAL computes; the HOL4 source
   contains no statement text to translate. -/

/- HOL4:
Theorem prim_type_sound_invariants:
  ∀type_ids sem_st prim_env.
    (sem_st,prim_env) = THE (prim_sem_env ffi) ∧
    DISJOINT type_ids {Tlist_num; Tbool_num; Texn_num}
    ⇒
    ?ctMap.
      type_sound_invariant sem_st prim_env ctMap FEMPTY type_ids prim_tenv ∧
      FRANGE ((SND o SND) o_f ctMap) ⊆ prim_type_ids
-/
-- HOL4 `THE NONE` is an unspecified value; Lean's `THE` needs an `Inhabited` instance, so the
-- default below plays that role. `prim_sem_env ffi0` is `SOME _`, so the default is never used.
theorem prim_type_sound_invariants {ffi : Type} (ffi0 : ffi_state ffi) :
    ∀ (type_ids : Set type_ident) (sem_st : cml_state ffi) (prim_env : sem_env),
      (sem_st, prim_env) =
          @THE _ ⟨({ clock := 0, ffi := ffi0, refs := [], next_type_stamp := 0,
                     next_exn_stamp := 0, eval_state_field := none },
                   .mk nsEmpty nsEmpty)⟩ (prim_sem_env ffi0) ∧
        DISJOINT type_ids (Set.insert Tlist_num (Set.insert Tbool_num {Texn_num})) →
      ∃ ctMap_ : ctMap,
        type_sound_invariant sem_st prim_env ctMap_ Finmap.FEMPTY type_ids prim_tenv ∧
        Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ prim_type_ids := by
  rintro type_ids sem_st prim_env ⟨h, hdisj⟩
  rw [prim_sem_env_eq] at h
  simp only [THE, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨prim_ctMap, ⟨prim_tenv_ok, prim_good_ctMap, prim_consistent_ctMap ffi0 type_ids hdisj,
    prim_type_all_env, prim_type_s ffi0⟩, ?_⟩
  intro x hx
  show x ∈ Tlist_num :: Tbool_num :: prim_type_nums
  rcases prim_ctMap_range hx with rfl | rfl | rfl <;> decide
