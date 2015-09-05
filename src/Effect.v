(** An effect is a type of command and a dependent type of answer. *)
Record t := New {
  command : Type;
  answer : command -> Type }.

(** The composition of two effects. *)
Definition compose (E1 E2 : t) : t :=
  New (command E1 + command E2) (fun c =>
    match c with
    | inl c1 => answer E1 c1
    | inr c2 => answer E2 c2
    end).
