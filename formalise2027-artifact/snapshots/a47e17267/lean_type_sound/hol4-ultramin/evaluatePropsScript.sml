(*
  Properties of the operational semantics.
*)
Theory evaluateProps
Ancestors
  ast evaluate namespace namespaceProps semanticPrimitives
  semanticPrimitivesProps
Libs
  preamble

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

Definition call_FFI_rel_def:
  call_FFI_rel s1 s2 <=> ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t
End

Definition dest_IO_event_def[simp]:
  dest_IO_event (IO_event s c b) = (s,c,b)
End

Definition io_events_mono_def:
  io_events_mono s1 s2 ⇔
    s1.io_events ≼ s2.io_events ∧
    (s2.io_events = s1.io_events ⇒ s2 = s1)
End

Theorem io_events_mono_trans:
   io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3
Proof
  rw[io_events_mono_def]
  \\ metis_tac[IS_PREFIX_TRANS, IS_PREFIX_ANTISYM]
QED

Theorem call_FFI_rel_io_events_mono:
   ∀s1 s2.
   RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2
Proof
  REWRITE_TAC[io_events_mono_def] \\
  ho_match_mp_tac RTC_INDUCT
  \\ simp[call_FFI_rel_def,ffiTheory.call_FFI_def]
  \\ rpt gen_tac \\ strip_tac
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[IS_PREFIX_APPEND]
QED

Theorem io_events_mono_refl[simp]:
   io_events_mono ffi ffi
Proof
  rw[io_events_mono_def]
QED

Theorem do_app_call_FFI_rel:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi'
Proof
  srw_tac[][do_app_cases,thunk_op_def,AllCaseEqs(),store_alloc_def] >> rw[] >>
  TRY FULL_CASE_TAC >>
  fs[option_case_eq] >>
  rpt (FULL_CASE_TAC \\ fs[]) >>
  match_mp_tac RTC_SUBSET >> rw[call_FFI_rel_def] >> fs[] >> every_case_tac
  >> fs[] >> metis_tac[]
QED

Theorem do_app_io_events_mono:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi'
Proof
  metis_tac[do_app_call_FFI_rel,call_FFI_rel_io_events_mono]
QED

Definition is_clock_io_mono_def:
  is_clock_io_mono f s = (case f s of (s', r) =>
        io_events_mono s.ffi s'.ffi
        /\ s'.clock <= s.clock
        /\ s.next_type_stamp <= s'.next_type_stamp
        /\ s.next_exn_stamp <= s'.next_exn_stamp
        /\ LENGTH s.refs <= LENGTH s'.refs
        /\ (!clk. case f (s with clock := clk) of (s'', r') =>
            (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> ~ (r = Rerr (Rabort Rtimeout_error))
                ==> r' = r
                    /\ s'' = (s' with clock := clk - (s.clock - s'.clock)))
            /\ (~ (r = Rerr (Rabort Rtimeout_error))
                ==> (clk >= s.clock - s'.clock
                    <=> ~ (r' = Rerr (Rabort Rtimeout_error))))
            /\ (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> clk <= s.clock
                ==> ~ (r = Rerr (Rabort Rtimeout_error)))
            /\ (clk <= s.clock ==> io_events_mono s''.ffi s'.ffi)
        ))
End

Theorem is_clock_io_mono_cong:
  s = t ==>
  (!s. s.eval_state = t.eval_state /\ s.refs = t.refs /\ s.ffi = t.ffi ==>
    f s = g s) ==>
  (is_clock_io_mono f s <=> is_clock_io_mono g t)
Proof
  simp [is_clock_io_mono_def]
QED

Theorem is_clock_io_mono_return:
   is_clock_io_mono (\s. (s,Rval r)) s
Proof
  fs [is_clock_io_mono_def]
QED

Theorem is_clock_io_mono_err:
   is_clock_io_mono (\s. (s,Rerr r)) s
Proof
  fs [is_clock_io_mono_def]
QED

Theorem pair_CASE_eq_forall:
   (case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b)
Proof
  Cases_on `x` \\ fs []
QED

Theorem is_clock_io_mono_bind:
   is_clock_io_mono f s /\ (!s' r. f s = (s', r)
        ==> is_clock_io_mono (g r) s')
    /\ (!s'. g (Rerr (Rabort Rtimeout_error)) s'
        = (s', Rerr (Rabort Rtimeout_error)))
    ==> is_clock_io_mono (\s. case f s of (s', r) => g r s') s
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [pair_case_eq] \\ fs []
  \\ simp_tac bool_ss [pair_CASE_eq_forall, pair_case_eq]
  \\ rpt (FIRST [DISCH_TAC, GEN_TAC])
  \\ full_simp_tac (bool_ss ++ pairSimps.PAIR_ss) []
  \\ fsrw_tac [SATISFY_ss] [io_events_mono_trans]
  \\ fs []
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [pair_CASE_eq_forall, pair_case_eq]
  \\ rpt (FIRST [first_x_assum drule, disch_tac,
      drule_then strip_assume_tac (METIS_PROVE [] ``(P ==> Q) ==> P \/ ~ P``)]
    \\ fs [] \\ rfs [])
  \\ fsrw_tac [SATISFY_ss] [io_events_mono_trans]
QED

Definition adj_clock_def:
  adj_clock inc dec s = (s with clock := ((s.clock + inc) - dec))
End

Theorem is_clock_io_mono_check:
   (~ (s.clock = 0) ==>
        is_clock_io_mono (\s. f (adj_clock 1 0 s)) (dec_clock s))
    ==> is_clock_io_mono (\s. if s.clock = 0
        then (s,Rerr (Rabort Rtimeout_error)) else f s) s
Proof
  fs [is_clock_io_mono_def, dec_clock_def, adj_clock_def, with_same_clock]
  \\ rpt (CASE_TAC ORELSE DISCH_TAC ORELSE GEN_TAC ORELSE CHANGED_TAC (fs []))
  \\ fs [pair_CASE_eq_forall]
  \\ first_x_assum (qspec_then `clk - 1` mp_tac)
  \\ simp []
  \\ rpt (CASE_TAC ORELSE DISCH_TAC ORELSE GEN_TAC ORELSE CHANGED_TAC (fs []))
  \\ Cases_on `r' = Rerr (Rabort Rtimeout_error)` \\ fs []
QED

Theorem dec_inc_clock:
  dec_clock (adj_clock 1 0 s) = s
Proof
  simp [dec_clock_def, adj_clock_def, with_same_clock]
QED

Theorem do_app_refs_length:
   do_app refs_ffi op vs = SOME res ==>
   LENGTH (FST refs_ffi) <= LENGTH (FST (FST res))
Proof
  rw [] \\ Cases_on `refs_ffi` \\ Cases_on `op`
  \\ gvs [do_app_def,thunk_op_def,AllCaseEqs(),store_assign_def]
  \\ fs [store_assign_def,store_alloc_def]
  \\ rveq \\ fs [] \\ rveq \\ fs[]
QED

Theorem is_clock_io_mono_do_app_simple:
  ! xs (st:'ffi state).
   is_clock_io_mono (\st'.
    case do_app (st'.refs, st'.ffi) op xs of
      NONE => (st', Rerr (Rabort Rtype_error))
    | SOME ((refs,ffi),r) =>
      (st' with<| refs := refs; ffi := ffi |>, list_result r)) st
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (CASE_TAC ORELSE CHANGED_TAC (fs []) ORELSE CHANGED_TAC rveq ORELSE gen_tac)
  \\ imp_res_tac do_app_refs_length \\ gs[]
  \\ metis_tac [do_app_io_events_mono]
QED

val step_tac =
  rpt (FIRST ([strip_tac]
    @ map ho_match_mp_tac [is_clock_io_mono_bind, is_clock_io_mono_check]
    @ [CHANGED_TAC (fs [Cong is_clock_io_mono_cong,
                        is_clock_io_mono_return, is_clock_io_mono_err,
                        do_eval_res_def, dec_inc_clock]), TOP_CASE_TAC]));

Theorem is_clock_io_mono_evaluate:
   (!(s : 'ffi state) env es. is_clock_io_mono (\s. evaluate s env es) s) /\
   (!(s : 'ffi state) env v pes err_v.
        is_clock_io_mono (\s. evaluate_match s env v pes err_v) s) /\
   (!(s : 'ffi state) env ds.
        is_clock_io_mono (\s. evaluate_decs s env ds) s)
Proof
 ho_match_mp_tac full_evaluate_ind
 \\ rpt strip_tac \\ fs [full_evaluate_def, combine_dec_result_def]
 \\ TRY (step_tac \\ NO_TAC)
 >- (
  ho_match_mp_tac is_clock_io_mono_bind \\ fs[]
  \\ rpt strip_tac
  \\ ntac 2 (TOP_CASE_TAC
            \\ fs [is_clock_io_mono_return, is_clock_io_mono_err])
  >-  (
    fs[Cong is_clock_io_mono_cong, do_eval_res_def]
    \\ ho_match_mp_tac is_clock_io_mono_bind
    \\ gs[]
    \\ rpt conj_tac
    \\ step_tac \\ gs[is_clock_io_mono_def, fix_clock_def])
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ rpt (FIRST [CHANGED_TAC (fs[is_clock_io_mono_return, is_clock_io_mono_err,
                                   is_clock_io_mono_do_app_simple]), CASE_TAC])
    \\ ho_match_mp_tac is_clock_io_mono_check \\ gs[] \\ rpt strip_tac
    \\ res_tac \\ gs[dec_inc_clock])
  >- (
    gvs [AllCaseEqs()]
    \\ step_tac
    \\ fs [is_clock_io_mono_def, dec_clock_def]
    \\ gvs [oneline update_thunk_def, oneline dest_thunk_def, store_assign_def,
            AllCaseEqs()])
  >- (assume_tac (SIMP_RULE std_ss [] is_clock_io_mono_do_app_simple) \\ fs[]))
 >- (step_tac \\ fs[is_clock_io_mono_def])
 >- (step_tac \\ fs[is_clock_io_mono_def])
 \\ step_tac \\ fs[is_clock_io_mono_def]
QED

Theorem is_clock_io_mono_evaluate_decs:
  !s e p. is_clock_io_mono (\s. evaluate_decs s e p) s
Proof
  fs [is_clock_io_mono_evaluate]
QED

Theorem is_clock_io_mono_extra:
   (!s. is_clock_io_mono f s)
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> f (s with clock := s.clock + extra)
        = (s' with clock := s'.clock + extra,r)
Proof
  DISCH_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with clock := s.clock + extra`)
  \\ fs [is_clock_io_mono_def]
  \\ CASE_TAC
  \\ rpt (DISCH_TAC ORELSE GEN_TAC)
  \\ fs []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s.clock`)
  \\ fs [semanticPrimitivesPropsTheory.with_same_clock]
  \\ rpt DISCH_TAC
  \\ rpt (CHANGED_TAC (fs [semanticPrimitivesPropsTheory.with_same_clock]))
QED

fun mk_extra_lemmas mp_rule monad_rule
  = BODY_CONJUNCTS monad_rule
    |> map (BETA_RULE o MATCH_MP mp_rule o Q.GEN `s`)
fun prove_extra mp_rule monad_rule
  = simp_tac bool_ss (mk_extra_lemmas mp_rule monad_rule)

Theorem list_result_eq_Rval[simp]:
  list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v
Proof
  Cases_on`r`>>srw_tac[][list_result_def,EQ_IMP_THM]
QED

Theorem evaluate_length:
   (∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1) ∧
   (∀(s:'ffi state) e ds s' r. evaluate_decs s e ds = (s',Rval r) ⇒ T)
Proof
  ho_match_mp_tac full_evaluate_ind >>
  srw_tac[][evaluate_def,LENGTH_NIL] >> srw_tac[][] >>
  gvs[AllCaseEqs()]
QED

val evaluate_decs_lemmas
  = BODY_CONJUNCTS is_clock_io_mono_evaluate_decs
    |> map (BETA_RULE o MATCH_MP is_clock_io_mono_extra o Q.GEN `s`)

(* due to Eval this is no longer true
Theorem evaluate_state_unchanged:
  (!(st:'ffi state) env es st' r.
    evaluate st env es = (st', r)
    ⇒
    st'.next_type_stamp = st.next_type_stamp ∧
    st'.next_exn_stamp = st.next_exn_stamp) ∧
  (!(st:'ffi state) env v pes err_v st' r.
    evaluate_match st env v pes err_v = (st', r)
    ⇒
    st'.next_type_stamp = st.next_type_stamp ∧
    st'.next_exn_stamp = st.next_exn_stamp)
Proof
 ho_match_mp_tac evaluate_ind
 >> rw [evaluate_def]
 >> every_case_tac
 >> fs []
 >> rw [dec_clock_def, shift_fp_opts_def]
QED
*)

Theorem is_clock_io_mono_set_clock:
   is_clock_io_mono f s
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> ?ck0. f (s with clock := ck0) = (s' with clock := ck1, r)
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `ck1 + (s.clock − (HD [s';s]).clock)`)
  \\ CASE_TAC
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ metis_tac []
QED

val evaluate_set_clock_lemmas
  = (BODY_CONJUNCTS is_clock_io_mono_evaluate
    @ BODY_CONJUNCTS is_clock_io_mono_evaluate_decs)
  |> map (BETA_RULE o MATCH_MP is_clock_io_mono_set_clock);

Theorem is_clock_io_mono_minimal:
   is_clock_io_mono f s
    ==> f s = (s', r) /\ s'.clock = 0 /\ r <> Rerr (Rabort Rtimeout_error)
        /\ s.clock > k
    ==> (?s''. f (s with clock := k) = (s'', Rerr (Rabort Rtimeout_error)) /\
               io_events_mono s''.ffi s'.ffi)
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`)
  \\ CASE_TAC \\ fs []
QED

Theorem can_pmatch_all_EVERY:
  can_pmatch_all envC refs ps v <=>
  EVERY (\p. pmatch envC refs p v [] <> Match_type_error) ps
Proof
  Induct_on `ps` \\ fs [can_pmatch_all_def]
QED

