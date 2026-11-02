import LeanTypeSound
open HOL4

/-! Run on the repaired translation (snapshot of the second repair round).
    HOL4 computes do_app_cases and type_op_cases by rewriting. The frozen baseline
    stated both as `P ↔ P`. The repaired translation states the case expansions.
    This file proves both statements from the Lean definitions and checks that
    they are the statements of the translation. -/

set_option maxHeartbeats 4000000 in
theorem type_op_cases_holds :
    ∀ (op_ : op) (ts : List sem_t) (t3 : sem_t),
      type_op op_ ts t3 ↔
        (∃ u1 u2, op_ = .Opapp ∧ ts = [u1, u2] ∧ u1 = Tfn u2 t3) ∨
        (∃ sh n u1, op_ = .Shift .W8 sh n ∧ ts = [u1] ∧ u1 = Tword8 ∧ t3 = Tword8) ∨
        (∃ sh n u1, op_ = .Shift .W64 sh n ∧ ts = [u1] ∧ u1 = Tword64 ∧ t3 = Tword64) ∨
        (∃ u1 u2, op_ = .Equality ∧ ts = [u1, u2] ∧ u1 = u2 ∧ t3 = Tbool) ∨
        (∃ a ty, op_ = .Arith a ty ∧ (∀ arg, arg ∈ ts → arg = t_of ty) ∧ t3 = t_of ty ∧
          supported_arith a ty = some ts.length) ∨
        (∃ ty1 ty2 u1, op_ = .FromTo ty1 ty2 ∧ ts = [u1] ∧ u1 = t_of ty1 ∧ t3 = t_of ty2 ∧
          supported_conversion ty1 ty2 = true) ∨
        (∃ tst ty u1 u2, op_ = .Test tst ty ∧ ts = [u1, u2] ∧ u1 = u2 ∧ t3 = Tbool ∧
          u1 = t_of ty ∧ supported_test tst ty = true) ∨
        (∃ u1 u2, op_ = .Opassign ∧ ts = [u1, u2] ∧ u1 = Tref u2 ∧ t3 = Ttup []) ∨
        (∃ u1, op_ = .Opref ∧ ts = [u1] ∧ t3 = Tref u1) ∨
        (∃ u1, op_ = .Opderef ∧ ts = [u1] ∧ u1 = Tref t3) ∨
        (∃ u1 u2, op_ = .Aw8alloc ∧ ts = [u1, u2] ∧ u1 = Tint ∧ u2 = Tword8 ∧ t3 = Tword8array) ∨
        (∃ u1 u2, op_ = .Aw8sub ∧ ts = [u1, u2] ∧ u1 = Tword8array ∧ u2 = Tint ∧ t3 = Tword8) ∨
        (∃ u1, op_ = .Aw8length ∧ ts = [u1] ∧ u1 = Tword8array ∧ t3 = Tint) ∨
        (∃ u1 u2 u3, op_ = .Aw8update ∧ ts = [u1, u2, u3] ∧ u1 = Tword8array ∧ u2 = Tint ∧
          u3 = Tword8 ∧ t3 = Ttup []) ∨
        (∃ u1 u2 u3, op_ = .CopyStrStr ∧ ts = [u1, u2, u3] ∧ u1 = Tstring ∧ u2 = Tint ∧
          u3 = Tint ∧ t3 = Tstring) ∨
        (∃ u1 u2 u3 u4 u5, op_ = .CopyStrAw8 ∧ ts = [u1, u2, u3, u4, u5] ∧ u1 = Tstring ∧
          u2 = Tint ∧ u3 = Tint ∧ u4 = Tword8array ∧ u5 = Tint ∧ t3 = Ttup []) ∨
        (∃ u1 u2 u3, op_ = .CopyAw8Str ∧ ts = [u1, u2, u3] ∧ u1 = Tword8array ∧ u2 = Tint ∧
          u3 = Tint ∧ t3 = Tstring) ∨
        (∃ u1 u2 u3 u4 u5, op_ = .CopyAw8Aw8 ∧ ts = [u1, u2, u3, u4, u5] ∧ u1 = Tword8array ∧
          u2 = Tint ∧ u3 = Tint ∧ u4 = Tword8array ∧ u5 = Tint ∧ t3 = Ttup []) ∨
        (∃ u1, op_ = .Implode ∧ ts = [u1] ∧ u1 = Tlist Tchar ∧ t3 = Tstring) ∨
        (∃ u1, op_ = .Explode ∧ ts = [u1] ∧ u1 = Tstring ∧ t3 = Tlist Tchar) ∨
        (∃ u1 u2, op_ = .Strsub ∧ ts = [u1, u2] ∧ u1 = Tstring ∧ u2 = Tint ∧ t3 = Tchar) ∨
        (∃ u1, op_ = .Strlen ∧ ts = [u1] ∧ u1 = Tstring ∧ t3 = Tint) ∨
        (∃ u1, op_ = .Strcat ∧ ts = [u1] ∧ u1 = Tlist Tstring ∧ t3 = Tstring) ∨
        (∃ u1 ctor, op_ = .VfromList ∧ ts = [.Tapp [u1] ctor] ∧ ctor = Tlist_num ∧
          t3 = Tvector u1) ∨
        (∃ u1 u2, op_ = .Vsub ∧ ts = [u1, u2] ∧ u2 = Tint ∧ Tvector t3 = u1) ∨
        (∃ u1 ctor, op_ = .Vlength ∧ ts = [.Tapp [u1] ctor] ∧ ctor = Tvector_num ∧ t3 = Tint) ∨
        (∃ u1 u2, op_ = .Aalloc ∧ ts = [u1, u2] ∧ u1 = Tint ∧ t3 = Tarray u2) ∨
        (∃ u1, op_ = .AallocEmpty ∧ ts = [u1] ∧ u1 = Ttup [] ∧ ∃ u2, t3 = Tarray u2) ∨
        (∃ u1 u2, op_ = .Asub ∧ ts = [u1, u2] ∧ u2 = Tint ∧ Tarray t3 = u1) ∨
        (∃ u1 ctor, op_ = .Alength ∧ ts = [.Tapp [u1] ctor] ∧ ctor = Tarray_num ∧ t3 = Tint) ∨
        (∃ u1 u2 u3, op_ = .Aupdate ∧ ts = [u1, u2, u3] ∧ u1 = Tarray u3 ∧ u2 = Tint ∧
          t3 = Ttup []) ∨
        (∃ u1 u2, op_ = .ConfigGC ∧ ts = [u1, u2] ∧ u1 = Tint ∧ u2 = Tint ∧ t3 = Ttup []) ∨
        (∃ nm u1 u2, op_ = .FFI nm ∧ ts = [u1, u2] ∧ u1 = Tstring ∧ u2 = Tword8array ∧
          t3 = Ttup []) ∨
        (∃ u1 ctor u2, op_ = .ListAppend ∧ ts = [.Tapp [u1] ctor, u2] ∧ ctor = Tlist_num ∧
          u2 = sem_t.Tapp [u1] ctor ∧ t3 = u2) := by
  intro op_ ts t3
  cases op_ <;> unfold type_op <;> split <;> simp_all [and_assoc]



/-! Faithful statement and proof of HOL4's computed theorem `do_app_cases`
(semanticPrimitivesPropsScript.sml). The right-hand side has one disjunct per
path through `do_app` that returns `some`, in the order of `do_app_def`. -/

/-- Close one disjunct `∃ xs, A ∧ B ∧ ...` from the local hypotheses.
    Witnesses are found by unification (`rfl`) or from a hypothesis. Fails fast. -/
syntax "solve_disj" : tactic
macro_rules
  | `(tactic| solve_disj) =>
    `(tactic| first
      | assumption
      | exact rfl
      | (constructor <;> solve_disj))

/-- Walk `D₁ ∨ D₂ ∨ ... ∨ Dₙ` and close the first disjunct that `solve_disj` proves. -/
syntax "pick_disj" : tactic
macro_rules
  | `(tactic| pick_disj) =>
    `(tactic| ((repeat (first | (left; solve_disj) | right)) <;> solve_disj))

/- HOL4: Theorem do_app_cases:
   Computed by HOL4 from do_app_def (SIMP_CONV with the case_eq theorems,
   COND_elim_ss, and PULL_EXISTS). Written here as that case expansion. -/
set_option maxHeartbeats 0 in
set_option linter.deprecated false in
theorem do_app_cases_holds {ffi : Type} :
    ∀ (s : List (store_v v)) (t : ffi_state ffi) (op_ : op) (vs : List v)
      (st' : List (store_v v) × ffi_state ffi) (r : result v v),
    do_app (s, t) op_ vs = some (st', r) ↔
    ( -- ListAppend
      (∃ x1 x2 xs ys, op_ = .ListAppend ∧ vs = [x1, x2] ∧
        v_to_list x1 = some xs ∧ v_to_list x2 = some ys ∧
        st' = (s, t) ∧ r = .Rval (list_to_v (xs ++ ys))) ∨
      -- Shift W8
      (∃ sh n w, op_ = .Shift .W8 sh n ∧ vs = [.Litv (.Word8 w)] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word8 (shift8_lookup sh w n)))) ∨
      -- Shift W64
      (∃ sh n w, op_ = .Shift .W64 sh n ∧ vs = [.Litv (.Word64 w)] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word64 (shift64_lookup sh w n)))) ∨
      -- Equality
      (∃ v1 v2 b, op_ = .Equality ∧ vs = [v1, v2] ∧
        do_eq v1 v2 = .Eq_val b ∧
        st' = (s, t) ∧ r = .Rval (Boolv b)) ∨
      -- Opassign
      (∃ b lnum val_ s', op_ = .Opassign ∧ vs = [.Loc b lnum, val_] ∧
        store_assign lnum (.Refv val_) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Opref
      (∃ val_ s' n, op_ = .Opref ∧ vs = [val_] ∧
        store_alloc (.Refv val_) s = (s', n) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true n)) ∨
      -- Opderef
      (∃ b n val_, op_ = .Opderef ∧ vs = [.Loc b n] ∧
        store_lookup n s = some (.Refv val_) ∧
        st' = (s, t) ∧ r = .Rval val_) ∨
      -- Aw8alloc
      (∃ n w, op_ = .Aw8alloc ∧ vs = [.Litv (.IntLit n), .Litv (.Word8 w)] ∧
        n < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ n w s' lnum, op_ = .Aw8alloc ∧ vs = [.Litv (.IntLit n), .Litv (.Word8 w)] ∧
        ¬ n < 0 ∧
        store_alloc (.W8array (REPLICATE n.natAbs w)) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- Aw8sub
      (∃ b lnum i ws, op_ = .Aw8sub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i ws, op_ = .Aw8sub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i ws, op_ = .Aw8sub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word8 (EL i.natAbs ws)))) ∨
      -- Aw8sub_unsafe
      (∃ b lnum i ws, op_ = .Aw8sub_unsafe ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word8 (EL i.natAbs ws)))) ∨
      -- Aw8length
      (∃ b n ws, op_ = .Aw8length ∧ vs = [.Loc b n] ∧
        store_lookup n s = some (.W8array ws) ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat ws.length)))) ∨
      -- Aw8update
      (∃ b lnum i w ws, op_ = .Aw8update ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i w ws, op_ = .Aw8update ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i w ws s', op_ = .Aw8update ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        store_assign lnum (.W8array (LUPDATE w i.natAbs ws)) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Aw8update_unsafe
      (∃ b lnum i w ws s', op_ = .Aw8update_unsafe ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        store_assign lnum (.W8array (LUPDATE w i.natAbs ws)) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- CopyStrStr
      (∃ strng off len, op_ = .CopyStrStr ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        copy_array (explode strng, off) len none = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng off len cs, op_ = .CopyStrStr ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        copy_array (explode strng, off) len none = some cs ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit (implode (String.mk cs))))) ∨
      -- CopyStrAw8
      (∃ strng off len b dst dstoff ws, op_ = .CopyStrAw8 ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b dst, .Litv (.IntLit dstoff)] ∧
        store_lookup dst s = some (.W8array ws) ∧
        copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng off len b dst dstoff ws cs s', op_ = .CopyStrAw8 ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b dst, .Litv (.IntLit dstoff)] ∧
        store_lookup dst s = some (.W8array ws) ∧
        copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = some cs ∧
        store_assign dst (.W8array (chars_to_ws cs)) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- CopyAw8Str
      (∃ b src off len ws, op_ = .CopyAw8Str ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        store_lookup src s = some (.W8array ws) ∧
        copy_array (ws, off) len none = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b src off len ws ws', op_ = .CopyAw8Str ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        store_lookup src s = some (.W8array ws) ∧
        copy_array (ws, off) len none = some ws' ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit (implode (String.mk (ws_to_chars ws')))))) ∨
      -- CopyAw8Aw8
      (∃ b src off len b' dst dstoff ws ds, op_ = .CopyAw8Aw8 ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b' dst, .Litv (.IntLit dstoff)] ∧
        store_lookup src s = some (.W8array ws) ∧
        store_lookup dst s = some (.W8array ds) ∧
        copy_array (ws, off) len (some (ds, dstoff)) = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b src off len b' dst dstoff ws ds ws' s', op_ = .CopyAw8Aw8 ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b' dst, .Litv (.IntLit dstoff)] ∧
        store_lookup src s = some (.W8array ws) ∧
        store_lookup dst s = some (.W8array ds) ∧
        copy_array (ws, off) len (some (ds, dstoff)) = some ws' ∧
        store_assign dst (.W8array ws') s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- XorAw8Str_unsafe
      (∃ b dst str_arg bs new_bs s', op_ = .XorAw8Str_unsafe ∧
        vs = [.Loc b dst, .Litv (.StrLit str_arg)] ∧
        store_lookup dst s = some (.W8array bs) ∧
        xor_bytes ((explode str_arg).map (fun c => n2w_8 (ORD c))) bs = some new_bs ∧
        store_assign dst (.W8array new_bs) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Implode
      (∃ val_ ls, op_ = .Implode ∧ vs = [val_] ∧
        v_to_char_list val_ = some ls ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit (implode (String.mk ls))))) ∨
      -- Explode
      (∃ strng, op_ = .Explode ∧ vs = [.Litv (.StrLit strng)] ∧
        st' = (s, t) ∧
        r = .Rval (list_to_v ((explode strng).map (fun c => .Litv (.Char c))))) ∨
      -- Strsub
      (∃ strng i, op_ = .Strsub ∧ vs = [.Litv (.StrLit strng), .Litv (.IntLit i)] ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng i, op_ = .Strsub ∧ vs = [.Litv (.StrLit strng), .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ i.natAbs ≥ strlen strng ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng i, op_ = .Strsub ∧ vs = [.Litv (.StrLit strng), .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ strlen strng ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Char (EL i.natAbs (explode strng))))) ∨
      -- Strlen
      (∃ strng, op_ = .Strlen ∧ vs = [.Litv (.StrLit strng)] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat (strlen strng))))) ∨
      -- Strcat
      (∃ val_ vs' strng, op_ = .Strcat ∧ vs = [val_] ∧
        v_to_list val_ = some vs' ∧
        vs_to_string vs' = some strng ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit strng))) ∨
      -- VfromList
      (∃ val_ vs', op_ = .VfromList ∧ vs = [val_] ∧
        v_to_list val_ = some vs' ∧
        st' = (s, t) ∧ r = .Rval (.Vectorv vs')) ∨
      -- Vsub_unsafe
      (∃ vs' i, op_ = .Vsub_unsafe ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        (0 ≤ i ∧ i.natAbs < vs'.length) ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Vsub
      (∃ vs' i, op_ = .Vsub ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ vs' i, op_ = .Vsub ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ vs' i, op_ = .Vsub ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Vlength
      (∃ vs', op_ = .Vlength ∧ vs = [.Vectorv vs'] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat vs'.length)))) ∨
      -- Aalloc
      (∃ n val_, op_ = .Aalloc ∧ vs = [.Litv (.IntLit n), val_] ∧
        n < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ n val_ s' lnum, op_ = .Aalloc ∧ vs = [.Litv (.IntLit n), val_] ∧
        ¬ n < 0 ∧
        store_alloc (.Varray (REPLICATE n.natAbs val_)) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- AallocEmpty
      (∃ s' lnum, op_ = .AallocEmpty ∧ vs = [.Conv none []] ∧
        store_alloc (.Varray []) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- AallocFixed (any argument list)
      (∃ s' lnum, op_ = .AallocFixed ∧
        store_alloc (.Varray vs) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- Asub
      (∃ b lnum i vs', op_ = .Asub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i vs', op_ = .Asub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i vs', op_ = .Asub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Asub_unsafe
      (∃ b lnum i vs', op_ = .Asub_unsafe ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Alength
      (∃ b n ws, op_ = .Alength ∧ vs = [.Loc b n] ∧
        store_lookup n s = some (.Varray ws) ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat ws.length)))) ∨
      -- Aupdate
      (∃ b lnum i val_ vs', op_ = .Aupdate ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i val_ vs', op_ = .Aupdate ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i val_ vs' s', op_ = .Aupdate ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        store_assign lnum (.Varray (LUPDATE val_ i.natAbs vs')) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Aupdate_unsafe
      (∃ b lnum i val_ vs' s', op_ = .Aupdate_unsafe ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        store_assign lnum (.Varray (LUPDATE val_ i.natAbs vs')) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- ConfigGC
      (∃ i j, op_ = .ConfigGC ∧ vs = [.Litv (.IntLit i), .Litv (.IntLit j)] ∧
        st' = (s, t) ∧ r = .Rval (.Conv none [])) ∨
      -- FFI
      (∃ n conf b lnum ws t' ws' s', op_ = .FFI n ∧
        vs = [.Litv (.StrLit conf), .Loc b lnum] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        call_FFI t (.ExtCall n) ((explode conf).map (fun c => n2w_8 (ORD c))) ws =
          .FFI_return t' ws' ∧
        store_assign lnum (.W8array ws') s = some s' ∧
        st' = (s', t') ∧ r = .Rval (.Conv none [])) ∨
      (∃ n conf b lnum ws outcome, op_ = .FFI n ∧
        vs = [.Litv (.StrLit conf), .Loc b lnum] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        call_FFI t (.ExtCall n) ((explode conf).map (fun c => n2w_8 (ORD c))) ws =
          .FFI_final outcome ∧
        st' = (s, t) ∧ r = .Rerr (.Rabort (.Rffi_error outcome))) ∨
      -- Env_id
      (∃ env gen id_, op_ = .Env_id ∧ vs = [.Env env (gen, id_)] ∧
        st' = (s, t) ∧ r = .Rval (.Conv none [nat_to_v gen, nat_to_v id_])) ∨
      (∃ gen id_, op_ = .Env_id ∧ vs = [.Conv none [gen, id_]] ∧
        st' = (s, t) ∧ r = .Rval (.Conv none [gen, id_])) ∨
      -- ThunkOp (any argument list; thunk_op_fun stays folded)
      (∃ th_op, op_ = .ThunkOp th_op ∧
        thunk_op_fun (s, t) th_op vs = some (st', r)) ∨
      -- Arith (any argument list)
      (∃ a ty res, op_ = .Arith a ty ∧
        EVERY (check_type ty) vs = true ∧
        do_arith a ty vs = some (.inr res) ∧
        st' = (s, t) ∧ r = .Rval res) ∨
      (∃ a ty exn, op_ = .Arith a ty ∧
        EVERY (check_type ty) vs = true ∧
        do_arith a ty vs = some (.inl exn) ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise exn)) ∨
      -- FromTo
      (∃ ty1 ty2 val_ res, op_ = .FromTo ty1 ty2 ∧ vs = [val_] ∧
        check_type ty1 val_ = true ∧
        do_conversion val_ ty1 ty2 = some (.inr res) ∧
        st' = (s, t) ∧ r = .Rval res) ∨
      (∃ ty1 ty2 val_ exn, op_ = .FromTo ty1 ty2 ∧ vs = [val_] ∧
        check_type ty1 val_ = true ∧
        do_conversion val_ ty1 ty2 = some (.inl exn) ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise exn)) ∨
      -- Test
      (∃ test_ test_ty v1 v2 b, op_ = .Test test_ test_ty ∧ vs = [v1, v2] ∧
        do_test test_ test_ty v1 v2 = .Eq_val b ∧
        st' = (s, t) ∧ r = .Rval (Boolv b))) := by
  intro s t op_ vs st' r
  constructor
  · -- (→) split every match and `if` of `do_app`, then pick the matching disjunct
    intro h
    dsimp only [do_app] at h
    split at h
    all_goals (repeat' (first | (dsimp only at h; split at h) | split at h))
    all_goals (try cases h)
    all_goals pick_disj
  · -- (←) for each disjunct, substitute the patterns and evaluate `do_app`
    intro h
    revert h
    simp only [or_imp, forall_exists_index, and_imp]
    and_intros
    all_goals (intros; subst_vars; simp only [do_app, *, and_self, ↓reduceIte])


example : type_of% @type_op_cases_thm = type_of% @type_op_cases_holds := rfl
set_option linter.deprecated false in
example : type_of% @do_app_cases = type_of% @do_app_cases_holds := rfl

-- The Docs proof of fix_clock_do_eval_res reached the admitted equality instance of
-- the baseline. Replayed here on the repaired translation, where equality on values
-- is structural, it still passes, so it did not depend on the admitted instance.
theorem fix_clock_do_eval_res_replay {ffi : Type}
    (s : cml_state ffi) (vs : List v) :
    fix_clock s (do_eval_res vs s) = do_eval_res vs s := by
  unfold fix_clock do_eval_res
  cases do_eval vs s.eval_state_field <;> simp
example : type_of% @fix_clock_do_eval_res = type_of% @fix_clock_do_eval_res_replay := rfl

#print axioms type_op_cases_holds
#print axioms do_app_cases_holds
#print axioms fix_clock_do_eval_res_replay
