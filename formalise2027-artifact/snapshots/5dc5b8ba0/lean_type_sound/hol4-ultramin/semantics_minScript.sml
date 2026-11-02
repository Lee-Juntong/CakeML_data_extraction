(*
  Minimized version of semanticsScript.sml for type soundness.
  Only includes evaluate_prog_with_clock and semantics_prog definitions,
  removing the parser/lexer dependencies (parse, semantics, semantics_init).
*)
Theory semantics_min
Ancestors
  evaluate lprefix_lub
Libs
  preamble

Definition evaluate_prog_with_clock_def:
  evaluate_prog_with_clock st env k prog =
    let (st',r) =
      evaluate_decs (st with clock := k) env prog
    in (st'.ffi,r)
End

Definition semantics_prog_def:
  (semantics_prog st env prog (Terminate outcome io_list) ⇔
    (* there is a clock for which evaluation terminates, either internally or via
       FFI, and the accumulated io events match the given io_list *)
    (?k ffi r.
      evaluate_prog_with_clock st env k prog = (ffi,r) ∧
      (case r of
       | Rerr (Rabort (Rffi_error outcome')) =>
         outcome = FFI_outcome (outcome')
       | r => r ≠ Rerr (Rabort Rtimeout_error) ∧ outcome = Success) ∧
      (io_list = ffi.io_events) ∧
      (r ≠ Rerr (Rabort Rtype_error)))) ∧
  (semantics_prog st env prog (Diverge io_trace) ⇔
    (* for all clocks, evaluation times out *)
    (!k. ?ffi.
      (evaluate_prog_with_clock st env k prog =
          (ffi, Rerr (Rabort Rtimeout_error)))) ∧
    (* the io_trace is the least upper bound of the set of traces
       produced for each clock *)
     lprefix_lub
       (IMAGE
         (λk. fromList (FST (evaluate_prog_with_clock st env k prog)).io_events)
         UNIV)
       io_trace) ∧
  (semantics_prog st env prog Fail ⇔
    (* there is a clock for which evaluation produces a runtime type error *)
    ∃k.
      SND(evaluate_prog_with_clock st env k prog) = Rerr (Rabort Rtype_error))
End
