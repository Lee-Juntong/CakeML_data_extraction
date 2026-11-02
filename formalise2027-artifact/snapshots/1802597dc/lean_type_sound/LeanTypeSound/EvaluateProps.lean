/-
  Translation of evaluatePropsScript.sml
  Properties of the operational semantics.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Evaluate
import LeanTypeSound.Namespace
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.SemanticPrimitivesProps

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition call_FFI_rel_def:
  call_FFI_rel s1 s2 <=> ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t
End
-/
def call_FFI_rel {ffi : Type} (s1 s2 : ffi_state ffi) : Prop :=
  ∃ n conf bytes t, call_FFI s1 n conf bytes = .FFI_return s2 t

/- HOL4:
Definition dest_IO_event_def[simp]:
  dest_IO_event (IO_event s c b) = (s,c,b)
End
-/
def dest_IO_event : io_event → ffiname × List word8 × List (word8 × word8)
  | .IO_event s c b => (s, c, b)

/- HOL4:
Definition io_events_mono_def:
  io_events_mono s1 s2 ⇔
    s1.io_events ≼ s2.io_events ∧
    (s2.io_events = s1.io_events ⇒ s2 = s1)
End
-/
def io_events_mono {ffi : Type} (s1 s2 : ffi_state ffi) : Prop :=
  s1.io_events.isPrefixOf s2.io_events ∧
  (s2.io_events = s1.io_events → s2 = s1)

/- HOL4:
Definition is_clock_io_mono_def:
  is_clock_io_mono f s = ...
End
-/
def is_clock_io_mono {ffi α : Type} (f : cml_state ffi → cml_state ffi × α)
    (s : cml_state ffi) : Prop := sorry

/- HOL4:
Definition adj_clock_def:
  adj_clock inc dec s = (s with clock := ((s.clock + inc) - dec))
End
-/
def adj_clock {ffi : Type} (inc dec_ : Nat) (s : cml_state ffi) : cml_state ffi :=
  { s with clock := s.clock + inc - dec_ }

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem io_events_mono_trans -/
theorem io_events_mono_trans : True := by sorry

/- HOL4: Theorem call_FFI_rel_io_events_mono -/
theorem call_FFI_rel_io_events_mono : True := by sorry

/- HOL4: Theorem io_events_mono_refl[simp] -/
theorem io_events_mono_refl : True := by sorry

/- HOL4: Theorem do_app_call_FFI_rel -/
theorem do_app_call_FFI_rel : True := by sorry

/- HOL4: Theorem do_app_io_events_mono -/
theorem do_app_io_events_mono : True := by sorry

/- HOL4: Theorem is_clock_io_mono_cong -/
theorem is_clock_io_mono_cong : True := by sorry

/- HOL4: Theorem is_clock_io_mono_return -/
theorem is_clock_io_mono_return : True := by sorry

/- HOL4: Theorem is_clock_io_mono_err -/
theorem is_clock_io_mono_err : True := by sorry

/- HOL4: Theorem is_clock_io_mono_bind -/
theorem is_clock_io_mono_bind : True := by sorry

/- HOL4: Theorem is_clock_io_mono_check -/
theorem is_clock_io_mono_check : True := by sorry

/- HOL4: Theorem dec_inc_clock -/
theorem dec_inc_clock : True := by sorry

/- HOL4: Theorem do_app_refs_length -/
theorem do_app_refs_length : True := by sorry

/- HOL4: Theorem is_clock_io_mono_do_app_simple -/
theorem is_clock_io_mono_do_app_simple : True := by sorry

/- HOL4: Theorem is_clock_io_mono_evaluate -/
theorem is_clock_io_mono_evaluate : True := by sorry

/- HOL4: Theorem is_clock_io_mono_evaluate_decs -/
theorem is_clock_io_mono_evaluate_decs : True := by sorry

/- HOL4: Theorem is_clock_io_mono_extra -/
theorem is_clock_io_mono_extra : True := by sorry

/- HOL4: Theorem list_result_eq_Rval[simp] -/
theorem list_result_eq_Rval : True := by sorry

/- HOL4: Theorem evaluate_length -/
theorem evaluate_length : True := by sorry

/- HOL4: Theorem is_clock_io_mono_set_clock -/
theorem is_clock_io_mono_set_clock : True := by sorry

/- HOL4: Theorem is_clock_io_mono_minimal -/
theorem is_clock_io_mono_minimal : True := by sorry

/- HOL4: Theorem can_pmatch_all_EVERY -/
theorem can_pmatch_all_EVERY : True := by sorry
