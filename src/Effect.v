(** An effect is a type of command and a dependent type of answer. *)
Record t := New {
  command : Type;
  answer : command -> Type }.
