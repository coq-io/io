(** Effects are a type of commands and the type of answers to these commands. *)
Record t := New {
  command : Type;
  answer : command -> Type }.
