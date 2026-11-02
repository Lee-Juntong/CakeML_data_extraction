Theory location

Datatype: locn = UNKNOWNpt | EOFpt | POSN num num
End

Definition locnrow_def:
  locnrow (POSN r c) = r
End
val _ = add_record_field ("row", “locnrow”)

Definition locn_rowupdate_def:
  locn_rowupdate f (POSN r c) = POSN (f r) c
End
val _ = add_record_fupdate ("row", “locn_rowupdate”)

Definition locncol_def:
  locncol (POSN r c) = c
End
val _ = add_record_field ("col", “locncol”)
Definition locn_colupdate_def:
  locn_colupdate f (POSN r c) = POSN r (f c)
End
val _ = add_record_fupdate ("col", “locn_colupdate”)

Datatype: locs = Locs locn locn
End

