(*
  Proofs about the namespace datatype.
*)
Theory namespaceProps
Ancestors
  ast namespace
Libs
  preamble

Theorem mk_id_surj:
   !id. ?p n. id = mk_id p n
Proof
 Induct_on `id`
 >> rw []
 >> metis_tac [mk_id_def]
QED

Theorem mk_id_thm:
   !id. mk_id (id_to_mods id) (id_to_n id) = id
Proof
 Induct_on `id`
 >> rw [id_to_mods_def, id_to_n_def, mk_id_def]
QED

Theorem nsSub_mono[mono]:
   (!x y z. R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2)
Proof
 Cases_on `e1`
 >> Cases_on `e2`
 >> simp [nsSub_def, nsLookup_def]
 >> rw []
 >> metis_tac []
QED

Theorem nsAll2_mono[mono]:
   (!x y z. R1 x y z ⇒ R2 x y z) ⇒ nsAll2 R1 e1 e2 ⇒ nsAll2 R2 e1 e2
Proof
 rw [nsAll2_def]
 >> irule nsSub_mono
 >> rw []
 >- metis_tac []
 >> qexists_tac `\x y z. R1 x z y`
 >> rw []
QED

Theorem nsLookup_nsEmpty[simp]:
   !id. nsLookup nsEmpty id = NONE
Proof
 Cases
 >> rw [nsLookup_def, nsEmpty_def]
QED

Theorem nsLookupMod_nsEmpty[simp]:
   !x y. nsLookupMod nsEmpty (x::y) = NONE
Proof
 rw [nsLookupMod_def, nsEmpty_def]
QED

Theorem nsAppend_nsEmpty[simp]:
   !env. nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env
Proof
 Cases
 >> rw [nsAppend_def, nsEmpty_def]
QED

Theorem alist_to_ns_nil[simp]:
   alist_to_ns [] = nsEmpty
Proof
 rw [alist_to_ns_def, nsEmpty_def]
QED

Theorem nsSub_nsEmpty[simp]:
   !r env. nsSub r nsEmpty env
Proof
 rw [nsSub_def]
 >> Induct_on `path`
 >> Cases_on `env`
 >> fs [nsLookupMod_def, nsEmpty_def]
QED

Theorem nsAll_nsEmpty[simp]:
   !f. nsAll f nsEmpty
Proof
 rw [nsEmpty_def, nsAll_def]
QED

Theorem nsAll2_nsEmpty[simp]:
   !f. nsAll2 f nsEmpty nsEmpty
Proof
 rw [nsEmpty_def, nsAll2_def]
QED

Theorem alist_to_ns_cons[simp]:
   !k v l. alist_to_ns ((k,v)::l) = nsBind k v (alist_to_ns l)
Proof
 rw [alist_to_ns_def, nsBind_def]
QED

Theorem nsAppend_nsBind[simp]:
   !k v e1 e2. nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2)
Proof
 Cases_on `e1`
 >> Cases_on `e2`
 >> rw [nsAppend_def, nsBind_def]
QED

Theorem nsAppend_assoc[simp]:
   !e1 e2 e3. nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3
Proof
 rpt Cases
 >> rw [nsAppend_def]
QED

Theorem nsLookup_nsBind[simp]:
   (!n v e. nsLookup (nsBind n v e) (Short n) = SOME v) ∧
   (!n n' v e. n ≠ Short n' ⇒ nsLookup (nsBind n' v e) n = nsLookup e n)
Proof
 rw []
 >> Cases_on `e`
 >> TRY (Cases_on `n`)
 >> rw [nsLookup_def, nsBind_def]
QED

Theorem nsAppend_nsSing[simp]:
   !n x e. nsAppend (nsSing n x) e = nsBind n x e
Proof
 rw [nsSing_def]
 >> Cases_on `e`
 >> simp [nsBind_def, nsAppend_def]
QED

Theorem nsLookup_nsSing[simp]:
   !n v id. nsLookup (nsSing n v) id = if id = Short n then SOME v else NONE
Proof
 rw [nsSing_def, nsLookup_def]
 >> Cases_on` id`
 >> fs [nsLookup_def]
QED

Theorem nsAll_nsSing[simp]:
   !R n v. nsAll R (nsSing n v) ⇔ R (Short n) v
Proof
 rw [nsAll_def, nsSing_def]
 >> eq_tac
 >> rw [nsLookup_def]
 >> Cases_on `id`
 >> fs [nsLookup_def]
QED

Theorem nsAll2_nsSing[simp]:
   !R n1 v1 n2 v2. nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ⇔ n1 = n2 ∧ R (Short n1) v1 v2
Proof
 rw [nsAll2_def, nsSub_def]
 >> eq_tac
 >- metis_tac []
 >> rw []
 >> rw []
 >> Cases_on `path`
 >> fs [nsSing_def, nsLookupMod_def]
QED

Theorem nsBind_11[simp]:
   !x y n x' y' n'. nsBind x y n = nsBind x' y' n' ⇔ x = x' ∧ y = y' ∧ n = n'
Proof
  rw [] >>
  Cases_on `n` >>
  Cases_on `n'` >>
  fs [nsBind_def] >>
  metis_tac []
QED

Theorem alist_to_ns_11[simp]:
   !l1 l2. alist_to_ns l1 = alist_to_ns l2 ⇔ l1 = l2
Proof
  rw [alist_to_ns_def]
QED

Theorem nsLookup_nsLift:
   !mn e id.
    nsLookup (nsLift mn e) id =
    case id of
    | Long mn' id' =>
      if mn = mn' then
        nsLookup e id'
      else
        NONE
    | Short _ => NONE
Proof
 rw [nsLift_def]
 >> CASE_TAC
 >> rw [nsLookup_def]
QED

Theorem nsLookupMod_nsLift:
   !mn e path.
    nsLookupMod (nsLift mn e) path =
    case path of
    | [] => SOME (nsLift mn e)
    | (mn'::path') =>
      if mn = mn' then
        nsLookupMod e path'
      else
        NONE
Proof
 rw [nsLift_def]
 >> CASE_TAC
 >> rw [nsLookupMod_def]
QED

Theorem nsLookup_nsAppend_some:
   ∀e1 id e2 v.
    nsLookup (nsAppend e1 e2) id = SOME v
    ⇔
    nsLookup e1 id = SOME v ∨
    (nsLookup e1 id = NONE ∧ nsLookup e2 id = SOME v ∧
     !p1 p2. p1 ≠ [] ∧ id_to_mods id = p1++p2 ⇒ nsLookupMod e1 p1 = NONE)
Proof
 ho_match_mp_tac nsLookup_ind
 >> rw []
 >> Cases_on `e2`
 >> fs [nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs [id_to_mods_def]
 >> eq_tac
 >> rw []
 >> fs []
 >- (
   Cases_on `p1`
   >> fs [nsLookupMod_def])
 >> first_x_assum (qspec_then `[mn]` mp_tac)
 >> simp [nsLookupMod_def]
QED

Theorem nsAppend_to_nsBindList:
   !l. nsAppend (alist_to_ns l) e = nsBindList l e
Proof
 Induct_on `l`
 >> fs [nsBindList_def, alist_to_ns_def]
 >> rw []
 >> pairarg_tac
 >> simp []
 >> Cases_on `e`
 >> fs [nsAppend_def]
 >> metis_tac [nsAppend_def, nsBind_def]
QED

Theorem nsLookupMod_nsAppend_none:
   !e1 e2 path.
    nsLookupMod (nsAppend e1 e2) path = NONE
    ⇔
    (nsLookupMod e1 path = NONE ∧
     (nsLookupMod e2 path = NONE ∨
      ?p1 p2 e3. p1 ≠ [] ∧ path = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3))
Proof
 Induct_on `path`
 >> rw []
 >> Cases_on `e2`
 >> Cases_on `e1`
 >> fs [nsAppend_def, nsLookupMod_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs []
 >> eq_tac
 >> rw []
 >- (
   Cases_on `p1`
   >> fs [nsLookupMod_def]
   >> rfs [])
 >> rw [METIS_PROVE [] ``x ∨ y ⇔ ~x ⇒ y``]
 >> qexists_tac `[h]`
 >> simp [nsLookupMod_def]
QED

Theorem eALL_T[simp]:
   !e. nsAll (\n x. T) e
Proof
 rw [nsAll_def]
QED

Theorem nsLookup_nsAll:
   !env x P v. nsAll P env ∧ nsLookup env x = SOME v ⇒ P x v
Proof
 rw [nsAll_def]
QED

Theorem nsAll_nsAppend:
   !f e1 e2. nsAll f e1 ∧ nsAll f e2 ⇒ nsAll f (nsAppend e1 e2)
Proof
 simp [nsAll_def, PULL_FORALL]
 >> rpt gen_tac
 >> qspec_tac (`v`, `v`)
 >> qspec_tac (`e2`, `e2`)
 >> qspec_tac (`id`, `id`)
 >> qspec_tac (`e1`, `e1`)
 >> ho_match_mp_tac nsLookup_ind
 >> rw []
 >> Cases_on `e2`
 >> fs [nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs [GSYM PULL_FORALL]
 >- metis_tac [nsLookup_def]
 >- metis_tac [nsLookup_def]
 >> rw []
 >> rpt (first_x_assum (qspec_then `Long mn id` mp_tac))
 >> simp [nsLookup_def]
QED

Theorem nsAll_alist_to_ns:
   !R l. EVERY (λ(n,v). R (Short n) v) l ⇒ nsAll R (alist_to_ns l)
Proof
 Induct_on `l`
 >> rw [nsAll_def, alist_to_ns_def]
 >> pairarg_tac
 >> fs []
 >> Cases_on `id`
 >> fs [nsLookup_def]
 >> every_case_tac
 >> fs [EVERY_MEM, LAMBDA_PROD, FORALL_PROD]
 >> rw []
 >> drule ALOOKUP_MEM
 >> metis_tac []
QED

Theorem nsAll_nsLift[simp]:
   !R mn e. nsAll R (nsLift mn e) ⇔ nsAll (\id. R (Long mn id)) e
Proof
 rw [nsAll_def, nsLookup_nsLift]
 >> eq_tac
 >> rw []
 >> every_case_tac
 >> fs []
QED

Theorem nsAll_nsAppend_left:
   !P n1 n2. nsAll P (nsAppend n1 n2) ⇒ nsAll P n1
Proof
  rw [nsAll_def] >>
  fs [nsLookup_nsAppend_some]
QED

Theorem nsSub_conj:
   !P Q e1 e2. nsSub (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsSub P e1 e2 ∧
  nsSub Q e1 e2
Proof
 rw [nsSub_def]
 >> eq_tac
 >> rw []
 >> metis_tac [SOME_11]
QED

Theorem nsSub_refl:
   !P R. (!n x. P n x ⇒ R n x x) ⇒ !e. nsAll P e ⇒ nsSub R e e
Proof
 rw [nsSub_def]
 >> metis_tac [nsLookup_nsAll]
QED

Theorem nsSub_nsBind:
   !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsSub R e1 e2 ⇒ nsSub R (nsBind x v1 e1) (nsBind x v2 e2)
Proof
 rw [nsBind_def, nsSub_def]
 >- (
   Cases_on `id = Short x`
   >> fs [])
 >> first_x_assum (qspec_then `path` mp_tac)
 >> Cases_on `path`
 >> fs [nsBind_def, nsLookupMod_def]
 >> Cases_on `e1`
 >> Cases_on `e2`
 >> fs [nsBind_def, nsLookupMod_def]
QED

Theorem nsSub_nsAppend2:
   !R e1 e2 e2'. nsSub R e1 e1 ∧ nsSub R e2 e2' ⇒ nsSub R (nsAppend e1 e2) (nsAppend e1 e2')
Proof
 rw [nsSub_def, nsLookup_nsAppend_some, nsLookupMod_nsAppend_none]
 >> rw [nsSub_def, nsLookup_nsAppend_some, nsLookupMod_nsAppend_none]
 >> metis_tac [NOT_SOME_NONE, SOME_11, option_nchotomy]
QED

Definition alist_rel_restr_def:
  (alist_rel_restr R l1 l2 [] ⇔ T) ∧
  (alist_rel_restr R l1 l2 (k1::keys) ⇔
    case ALOOKUP l1 k1 of
    | NONE => F
    | SOME v1 =>
      case ALOOKUP l2 k1 of
      | NONE => F
      | SOME v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys)
End

Theorem alist_rel_restr_thm:
   !R e1 e2 keys.
    alist_rel_restr R e1 e2 keys ⇔
      !k. MEM k keys ⇒ ?v1 v2. ALOOKUP e1 k = SOME v1 ∧ ALOOKUP e2 k = SOME v2 ∧ R k v1 v2
Proof
 Induct_on `keys`
 >> rw [alist_rel_restr_def]
 >> every_case_tac
 >> fs []
 >> metis_tac [NOT_SOME_NONE, SOME_11, option_nchotomy]
QED

Definition alistSub_def:
  alistSub R e1 e2 ⇔ alist_rel_restr R e1 e2 (MAP FST e1)
End

Theorem alistSub_cong:
   !l1 l2 l1' l2' R R'.
    l1 = l1' ∧ l2 = l2' ∧ (!n x y. ALOOKUP l1' n = SOME x ∧ ALOOKUP l2' n = SOME y ⇒ R n x y = R' n x y) ⇒
    (alistSub R l1 l2 ⇔ alistSub R' l1' l2')
Proof
  rw [alistSub_def]
  >> qspec_tac (`MAP FST l1`, `keys`)
  >> Induct
  >> rw [alist_rel_restr_def]
  >> every_case_tac
  >> metis_tac []
QED

val _ = DefnBase.export_cong "alistSub_cong";

Definition nsSub_compute_def:
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
End

Theorem nsLookup_FOLDR_nsLift:
   !e p k. nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Short k)
Proof
 Induct_on `p`
 >> rw [mk_id_def, nsLookup_def, nsLift_def]
QED

Theorem nsLookup_FOLDR_nsLift_some:
   !e p id v.
    nsLookup (FOLDR nsLift e p) id = SOME v ⇔
    (p = [] ∧ nsLookup e id = SOME v) ∨
    (p ≠ [] ∧ ?p2 n. id = mk_id (p++p2) n ∧ nsLookup e (mk_id p2 n) = SOME v)
Proof
 Induct_on `p`
 >> rw [nsLift_def]
 >> Cases_on `id`
 >> rw [nsLookup_def, mk_id_def]
 >> Cases_on `p`
 >> rw []
 >> eq_tac
 >> rw []
 >> rw []
 >> qexists_tac `id_to_mods i`
 >> qexists_tac `id_to_n i`
 >> rw [mk_id_thm]
QED

Theorem nsLookupMod_FOLDR_nsLift_none:
   !e p1 p2. nsLookupMod (FOLDR nsLift e p1) p2 = NONE ⇔
    (IS_PREFIX p1 p2 ∨ IS_PREFIX p2 p1) ⇒
    ?p3. p2 = p1++p3 ∧ nsLookupMod e p3 = NONE
Proof
 Induct_on `p1`
 >> rw [nsLift_def]
 >> Cases_on `p2`
 >> rw [nsLookupMod_def, mk_id_def]
QED

(*
Theorem nsSub_compute_thm_general:
   !p R e1 e2.
    nsSub R (FOLDR nsLift e1 (REVERSE p)) (FOLDR nsLift e2 (REVERSE p)) ⇔
    nsSub_compute p R e1 e2
Proof
 ho_match_mp_tac (theorem "nsSub_compute_ind")
 >> rw [nsSub_def, nsSub_compute_def, alistSub_def, alist_rel_restr_thm, nsLookup_def]
 >> eq_tac
 >> rw []
 >- (
   `?v1. ALOOKUP e1V k = SOME v1` by metis_tac [option_nchotomy, ALOOKUP_NONE]
   >> last_x_assum (qspec_then `mk_id (REVERSE p) k` mp_tac)
   >> simp [nsLookup_FOLDR_nsLift, nsLookup_def])
 >- (
   `?v1. ALOOKUP e1M k = SOME v1` by metis_tac [option_nchotomy, ALOOKUP_NONE]
   >> last_assum (qspec_then `REVERSE (k::p)` assume_tac)
   >> fs [nsLookupMod_FOLDR_nsLift_none, nsLookupMod_def]
   >> every_case_tac
   >> fs []
   >> first_x_assum drule
   >> disch_then drule
   >> disch_then (strip_assume_tac o GSYM)
   >> simp []
   >> pop_assum kall_tac
   >> rw []
   >- (
     fs [nsLookup_FOLDR_nsLift_some]
     >> first_x_assum (qspec_then `mk_id (REVERSE p++[k]++p2) n` mp_tac)
     >> Cases_on `p=[]`
     >> simp [nsLookup_def, mk_id_def])
   >> fs []
   >> rw []
   >- (
     `p3 = []`
       by (
         fs [IS_PREFIX_THM]
         >> `LENGTH p3 = 0` by decide_tac
         >> Cases_on `p3`
         >> fs [])
     >> fs [nsLookupMod_def])
   >- (
     fs [nsLookupMod_FOLDR_nsLift_none]
     >> rw []
     >> fs []
     >> rw []
     >> last_x_assum (qspec_then `REVERSE p++[k]++p3` mp_tac)
     >> rw []
     >> fs [nsLookupMod_def]
     >> every_case_tac
     >> fs []
     >> rw []
     >> metis_tac [IS_PREFIX_APPEND3, APPEND_ASSOC]))
 >- (
   fs [nsLookup_FOLDR_nsLift_some]
   >> rw []
   >> fs [mk_id_def]
   >- (
     Cases_on `id`
     >> fs [nsLookup_def]
     >- (
       drule ALOOKUP_MEM
       >> rw []
       >> fs [MEM_MAP, PULL_EXISTS]
       >> first_x_assum drule
       >> simp [])
     >> every_case_tac
     >> fs []
     >> drule ALOOKUP_MEM
     >> strip_tac
     >> fs [MEM_MAP, PULL_EXISTS]
     >> first_x_assum drule
     >> fs []
     >> first_x_assum drule
     >> disch_then drule
     >> disch_then (strip_assume_tac o GSYM)
     >> simp []
     >> pop_assum kall_tac
     >> rw []
     >> metis_tac [mk_id_surj])
   >- (
     Cases_on `p2`
     >> fs [nsLookup_def, mk_id_def]
     >- (
       drule ALOOKUP_MEM
       >> rw []
       >> fs [MEM_MAP, PULL_EXISTS]
       >> first_x_assum drule
       >> simp [])
     >> every_case_tac
     >> fs []
     >> drule ALOOKUP_MEM
     >> strip_tac
     >> fs [MEM_MAP, PULL_EXISTS]
     >> first_x_assum drule
     >> fs []
     >> first_x_assum drule
     >> disch_then drule
     >> disch_then (strip_assume_tac o GSYM)
     >> simp []
     >> pop_assum kall_tac
     >> rw []
     >> first_x_assum drule
     >> rw []
     >> full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]))
 >- (
   fs [nsLookupMod_FOLDR_nsLift_none]
   >> rw []
   >> fs []
   >> rw []
   >> fs []
   >- (
     `p3 = []`
       by (
         fs [IS_PREFIX_THM]
         >> `LENGTH p3 = 0` by decide_tac
         >> Cases_on `p3`
         >> fs [])
      >> fs [nsLookupMod_def])
   >> CCONTR_TAC
   >> fs []
   >> `?x. nsLookupMod (Bind e1V e1M) p3 = SOME x` by metis_tac [option_nchotomy]
   >> fs []
   >> pop_assum mp_tac
   >> Cases_on `p3`
   >> fs [nsLookupMod_def]
   >> CASE_TAC
   >> rw []
   >> fs [MEM_MAP, PULL_EXISTS]
   >> drule ALOOKUP_MEM
   >> rw []
   >> first_x_assum drule
   >> rw []
   >> fs []
   >> first_x_assum drule
   >> disch_then drule
   >> disch_then (strip_assume_tac o GSYM)
   >> fs []
   >> pop_assum kall_tac
   >> first_x_assum (qspec_then `REVERSE p ++ [h] ++ t` mp_tac)
   >> rw [])
QED

Theorem nsSub_compute_thm:
   !R e1 e2. nsSub R e1 e2 ⇔ nsSub_compute [] R e1 e2
Proof
 rw [GSYM nsSub_compute_thm_general]
QED
*)

Theorem nsAll2_conj:
   !P Q e1 e2. nsAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2
Proof
 rw [nsAll2_def, nsSub_conj]
 >> metis_tac []
QED

Theorem nsAll2_nsLookup2:
   !R e1 e2 n v2.
    nsLookup e2 n = SOME v2 ∧
    nsAll2 R e1 e2
    ⇒
    ?v1. nsLookup e1 n = SOME v1 ∧ R n v1 v2
Proof
 rw [nsSub_def, nsAll2_def]
 >> metis_tac [NOT_SOME_NONE, option_nchotomy, SOME_11]
QED

Theorem nsAll2_nsLookup_none:
   !R e1 e2 n.
    nsAll2 R e1 e2
    ⇒
    (nsLookup e1 n = NONE ⇔ nsLookup e2 n = NONE)
Proof
 rw [nsSub_def, nsAll2_def]
 >> metis_tac [NOT_SOME_NONE, option_nchotomy, SOME_11]
QED

Theorem nsAll2_nsBind:
   !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsAll2 R e1 e2 ⇒ nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2)
Proof
 rw [nsAll2_def]
 >> irule nsSub_nsBind
 >> rw []
QED

Theorem nsAll2_nsBindList:
   !R l1 l2 e1 e2.
     LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2
     ⇒
     nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2)
Proof
 Induct_on `l1`
 >> rw [nsBindList_def]
 >> rw [nsBindList_def]
 >> pairarg_tac
 >> rw []
 >> pairarg_tac
 >> rw []
 >> fs [nsBindList_def]
 >> irule nsAll2_nsBind
 >> rw []
QED

Theorem nsAll2_nsAppend:
   !R e1 e1' e2 e2'.
    nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' ⇒ nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2')
Proof
 rw [nsAll2_def, nsSub_def, nsLookup_nsAppend_some, nsLookupMod_nsAppend_none]
 >> metis_tac [NOT_SOME_NONE, SOME_11, option_nchotomy]
QED

Theorem nsAll2_alist_to_ns:
   !R l1 l2. LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ⇒ nsAll2 R (alist_to_ns l1) (alist_to_ns l2)
Proof
 Induct_on `l1`
 >> rw []
 >> pairarg_tac
 >> fs []
 >> pairarg_tac
 >> fs []
 >> rw []
 >> irule nsAll2_nsBind
 >> simp []
QED

Theorem nsAll2_nsLift[simp]:
   !R mn e1 e2. nsAll2 R (nsLift mn e1) (nsLift mn e2) ⇔ nsAll2 (\id. R (Long mn id)) e1 e2
Proof
 rw [nsAll2_def, nsSub_def]
 >> eq_tac
 >> rw []
 >- (
   last_x_assum (qspec_then `Long mn id` mp_tac)
   >> simp [nsLookup_nsLift, nsLookupMod_nsLift])
 >- (
   last_x_assum (qspec_then `mn::path` mp_tac)
   >> simp [nsLookup_nsLift, nsLookupMod_nsLift])
 >- (
   first_x_assum (qspec_then `Long mn id` mp_tac)
   >> simp [nsLookup_nsLift, nsLookupMod_nsLift])
 >- (
   first_x_assum (qspec_then `mn::path` mp_tac)
   >> simp [nsLookup_nsLift, nsLookupMod_nsLift])
 >> pop_assum mp_tac
 >> simp [nsLookup_nsLift, nsLookupMod_nsLift]
 >> every_case_tac
 >> fs []
QED

