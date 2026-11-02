(*
   Proof tools (e.g. tactics) used throughout the development.
   Minimized: removed unused functions and imports.
*)
structure preamble =
struct
local open intLib wordsLib in end;
open set_relationTheory; (* comes first so relationTheory takes precedence *)
open ASCIInumbersTheory BasicProvers Defn HolKernel Parse SatisfySimps Tactic
     monadsyntax alistTheory alignmentTheory arithmeticTheory bagTheory boolLib
     boolSimps bossLib byteTheory containerTheory combinTheory dep_rewrite
     finite_mapTheory indexedListsTheory listTheory llistTheory
     lprefix_lubTheory markerLib miscTheory mp_then optionTheory pairLib
     pairTheory pred_setTheory quantHeuristicsLib relationTheory res_quanTheory
     rich_listTheory sortingTheory sptreeTheory stringTheory sumTheory
     wordsTheory;
fun clear_cache_prover gtac  =
 let
   val _ = List.app Cache.clear_cache [numSimps.arith_cache, intSimps.omega_cache,
                                       intSimps.cooper_cache]
   val res = TAC_PROOF gtac
   val _ = List.app Cache.clear_cache [numSimps.arith_cache, intSimps.omega_cache,
                                       intSimps.cooper_cache]
 in
   res
 end
val _ = Tactical.set_prover clear_cache_prover;

val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val match_exists_tac = part_match_exists_tac (hd o strip_conj)
val asm_exists_tac = first_assum(match_exists_tac o concl)

infix 8 $
fun op $ (f,x) = f x

val _ = set_trace"Goalstack.print_goal_at_top"0 handle HOL_ERR _ => set_trace"goalstack print goal at top"0

val rveq = rpt BasicProvers.VAR_EQ_TAC

end

