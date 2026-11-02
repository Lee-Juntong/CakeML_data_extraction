(*
  Various basic properties of the semantic primitives.
*)
Theory semanticPrimitivesProps
Ancestors
  ast namespace ffi semanticPrimitives namespaceProps
Libs
  preamble boolSimps

Theorem with_same_v[simp]:
   (env:'v sem_env) with v := env.v = env
Proof
  srw_tac[][sem_env_component_equality]
QED

Theorem unchanged_env[simp]:
  !(env : 'a sem_env).
  <| v := env.v; c := env.c |> = env
Proof
 rw [sem_env_component_equality]
QED

Theorem with_same_clock:
   (st:'ffi semanticPrimitives$state) with clock := st.clock = st
Proof
  rw[semanticPrimitivesTheory.state_component_equality]
QED

Theorem Boolv_11[simp]:
  Boolv b1 = Boolv b2 ⇔ (b1 = b2)
Proof
srw_tac[][Boolv_def]
QED

Theorem extend_dec_env_assoc[simp]:
   !env1 env2 env3.
    extend_dec_env env1 (extend_dec_env env2 env3)
    =
    extend_dec_env (extend_dec_env env1 env2) env3
Proof
 rw [extend_dec_env_def]
QED

Definition shift_lookup_def[simp]:
  (shift_lookup Lsl = word_lsl) ∧
  (shift_lookup Lsr = word_lsr) ∧
  (shift_lookup Asr = word_asr) ∧
  (shift_lookup Ror = word_ror)
End

(*
Definition do_word_op_def[simp]:
  (do_word_op op W8 (Word8 w1) (Word8 w2) = SOME (Word8 (opw_lookup op w1 w2))) ∧
  (do_word_op op W64 (Word64 w1) (Word64 w2) = SOME (Word64 (opw_lookup op w1 w2))) ∧
  (do_word_op op _ _ _ = NONE)
End

Definition do_word_to_int_def[simp]:
  (do_word_to_int W8 (Word8 w) = SOME(int_of_num(w2n w))) ∧
  (do_word_to_int W64 (Word64 w) = SOME(int_of_num(w2n w))) ∧
  (do_word_to_int _ _ = NONE)
End

Definition do_word_from_int_def[simp]:
  (do_word_from_int W8 i = Word8 (i2w i)) ∧
  (do_word_from_int W64 i = Word64 (i2w i))
End
*)

Theorem pat_bindings_accum:
 (!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) ∧
 (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc)
Proof
  Induct
  >- srw_tac[][pat_bindings_def]
  >- srw_tac[][pat_bindings_def]
  >- srw_tac[][pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, CONS_APPEND, pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, CONS_APPEND, pat_bindings_def]
  >- srw_tac[][pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]
QED

val eqs = LIST_CONJ (map TypeBase.case_eq_of
  [``:op``, ``:'a list``, ``:'a option``, ``:v``, ``:'a store_v``, ``:lit``,
   ``:eq_result``, ``:word_size``])

Theorem pair_case_eq[local]:
  pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v
Proof
  Cases_on `x` >>
 srw_tac[][]
QED

Theorem pair_lam_lem[local]:
  !f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)
Proof
  srw_tac[][]
QED

Theorem do_app_cases =
  ``do_app (s,t) op vs = SOME (st',v)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV)

Theorem build_rec_env_help_lem[local]:
  ∀funs env funs'.
    FOLDR (λ(f,x,e) env'. nsBind f (Recclosure env funs' f) env') env' funs =
    nsAppend (alist_to_ns (MAP (λ(f,n,e). (f, Recclosure env funs' f)) funs)) env'
Proof
  Induct >>
 srw_tac[][] >>
 PairCases_on `h` >>
 srw_tac[][]
QED

(* Alternate definition for build_rec_env *)
Theorem build_rec_env_merge:
 ∀funs funs' env env'.
  build_rec_env funs env env' =
  nsAppend (alist_to_ns (MAP (λ(f,n,e). (f, Recclosure env funs f)) funs)) env'
Proof
srw_tac[][build_rec_env_def, build_rec_env_help_lem]
QED

Theorem do_con_check_build_conv:
 !tenvC cn vs l.
  do_con_check tenvC cn l ⇒ ?v. build_conv tenvC cn vs = SOME v
Proof
srw_tac[][do_con_check_def, build_conv_def] >>
every_case_tac >>
full_simp_tac(srw_ss())[]
QED

Definition map_error_result_def[simp]:
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f (Rabort a) = Rabort a)
End

Definition map_result_def[simp]:
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))
End

Definition every_error_result_def[simp]:
  (every_error_result P (Rraise e) = P e) ∧
  (every_error_result P (Rabort a) = T)
End

Definition every_result_def[simp]:
  (every_result P1 P2 (Rval v) = (P1 v)) ∧
  (every_result P1 P2 (Rerr e) = (every_error_result P2 e))
End

Definition map_sv_def[simp]:
  map_sv f (Refv v) = Refv (f v) ∧
  map_sv _ (W8array w) = (W8array w) ∧
  map_sv f (Varray vs) = (Varray (MAP f vs)) ∧
  map_sv f (Thunk m v) = (Thunk m (f v))
End

Definition dest_Refv_def[simp]:
  dest_Refv (Refv v) = v
End

Definition store_v_vs_def[simp]:
  store_v_vs (Refv v) = [v] ∧
  store_v_vs (Varray vs) = vs ∧
  store_v_vs (W8array _) = [] ∧
  store_v_vs (Thunk _ v) = [v]
End

Definition ctors_of_tdef_def[simp]:
  ctors_of_tdef (_,_,condefs) = MAP FST condefs
End

(* free vars *)

Definition FV_def[simp]:
  (FV (Raise e) = FV e) ∧
  (FV (Handle e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Lit _) = {}) ∧
  (FV (Con _ ls) = FV_list ls) ∧
  (FV (Var id) = {id}) ∧
  (FV (Fun x e) = FV e DIFF {Short x}) ∧
  (FV (App _ es) = FV_list es) ∧
  (FV (Log _ e1 e2) = FV e1 ∪ FV e2) ∧
  (FV (If e1 e2 e3) = FV e1 ∪ FV e2 ∪ FV e3) ∧
  (FV (Mat e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Let xo e b) = FV e ∪ (FV b DIFF (case xo of NONE => {} | SOME x => {Short x}))) ∧
  (FV (Letrec defs b) = FV_defs defs ∪ FV b DIFF set (MAP (Short o FST) defs)) ∧
  (FV (Tannot e t) = FV e) ∧
  (FV (Lannot e l) = FV e) ∧
  (FV_list [] = {}) ∧
  (FV_list (e::es) = FV e ∪ FV_list es) ∧
  (FV_pes [] = {}) ∧
  (FV_pes ((p,e)::pes) =
     (FV e DIFF (IMAGE Short (set (pat_bindings p [])))) ∪ FV_pes pes) ∧
  (FV_defs [] = {}) ∧
  (FV_defs ((_,x,e)::defs) =
     (FV e DIFF {Short x}) ∪ FV_defs defs)
End

Theorem FV_pes_MAP:
   FV_pes pes = BIGUNION (IMAGE (λ(p,e). FV e DIFF (IMAGE Short (set (pat_bindings p [])))) (set pes))
Proof
  Induct_on`pes`>>simp[]>>
  qx_gen_tac`p`>>PairCases_on`p`>>srw_tac[][]
QED

Theorem FV_defs_MAP:
   ∀ls. FV_defs ls = BIGUNION (IMAGE (λ(f,x,e). FV e DIFF {Short x}) (set ls))
Proof
  Induct_on`ls`>>simp[FORALL_PROD]
QED

Definition FV_dec_def[simp]:
  (FV_dec (Dlet locs p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec locs defs) = FV (Letrec defs (Lit ARB)))∧
  (FV_dec (Dtype _ _) = {}) ∧
  (FV_dec (Dtabbrev _ _ _ _) = {}) ∧
  (FV_dec (Dexn _ _ _) = {})
End

Theorem concrete_v_list[simp]:
  !xs. concrete_v_list xs = EVERY concrete_v xs
Proof
  Induct \\ simp [concrete_v_def]
QED

Theorem prim_type_cases:
  ∀ty.
    ty = BoolT ∨
    ty = IntT ∨
    ty = CharT ∨
    ty = StrT ∨
    ty = WordT W8 ∨
    ty = WordT W64 ∨
    ty = Float64T
Proof
  Cases \\ fs [] \\ Cases_on ‘w’ \\ fs []
QED

