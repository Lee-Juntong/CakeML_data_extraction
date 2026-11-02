/-
  Translation of semantics_minScript.sml
  Minimized version of semanticsScript.sml for type soundness.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Evaluate
import LeanTypeSound.LprefixLub
import LeanTypeSound.Ffi

open HOL4

/- HOL4:
Definition evaluate_prog_with_clock_def:
  evaluate_prog_with_clock st env k prog =
    let (st',r) =
      evaluate_decs (st with clock := k) env prog
    in (st'.ffi,r)
End
-/
def evaluate_prog_with_clock {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (k : Nat) (prog : List dec) : ffi_state ffi × result sem_env v :=
  let (st', r) := evaluate_decs ({ st with clock := k }) env prog
  (st'.ffi, r)

/- HOL4:
Definition semantics_prog_def:
  (semantics_prog st env prog (Terminate outcome io_list) ⇔ ...) ∧
  (semantics_prog st env prog (Diverge io_trace) ⇔ ...) ∧
  (semantics_prog st env prog Fail ⇔ ...)
End
-/
def semantics_prog {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (prog : List dec) : behaviour → Prop
  | .Terminate out io_list =>
    ∃ k ffi_ r,
      evaluate_prog_with_clock st env k prog = (ffi_, r) ∧
      (match r with
       | .Rerr (.Rabort (.Rffi_error outcome')) => out = .FFI_outcome outcome'
       | r => r ≠ .Rerr (.Rabort .Rtimeout_error) ∧ out = .Success) ∧
      io_list = ffi_.io_events ∧
      r ≠ .Rerr (.Rabort .Rtype_error)
  | .Diverge io_trace =>
    (∀ k, ∃ ffi_,
      evaluate_prog_with_clock st env k prog =
        (ffi_, .Rerr (.Rabort .Rtimeout_error))) ∧
    lprefix_lub
      (Set.image
        (fun k => LazyList.fromList (evaluate_prog_with_clock st env k prog).1.io_events)
        Set.univ)
      io_trace
  | .Fail =>
    ∃ k,
      (evaluate_prog_with_clock st env k prog).2 = .Rerr (.Rabort .Rtype_error)
