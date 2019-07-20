Require C.
Require Effect.

(** A run is an execution of a computation with answers to the calls. *)
Inductive t {E : Effect.t} : forall {A : Type}, C.t E A -> A -> Type :=
| Ret : forall {A} (x : A), t (C.Ret (E := E) x) x
| Call : forall (c : Effect.command E) (a : Effect.answer E c), t (C.Call c) a
| Let : forall {A B} {c_x : C.t E A} {x : A} {c_f : A -> C.t E B} {y : B},
  t c_x x -> t (c_f x) y -> t (C.Let c_x c_f) y
| ChooseLeft : forall {A} {c_x1 c_x2 : C.t E A} {x1 : A},
  t c_x1 x1 -> t (C.Choose c_x1 c_x2) x1
| ChooseRight : forall {A} {c_x1 c_x2 : C.t E A} {x2 : A},
  t c_x2 x2 -> t (C.Choose c_x1 c_x2) x2
| Join : forall {A B} {c_x : C.t E A} {x : A} {c_y : C.t E B} {y : B},
  t c_x x -> t c_y y -> t (C.Join c_x c_y) (x, y).

Module Notations.
  Definition ret {E A} (v : A) : t (E := E) (C.Ret v) v :=
    Ret v.

  Definition call (E : Effect.t) (c : Effect.command E) (a : Effect.answer E c)
    : t (C.Call c) a :=
    Call c a.

  (** A nicer notation for `Let`. *)
  Notation "'rlet!' X 'in' Y" :=
    (Let X Y)
    (at level 200, X at level 100, Y at level 200).

  (** Let ignoring the unit answer. *)
  Notation "'rdo!' X 'in' Y" :=
    (Let (A := unit) X Y)
    (at level 200, X at level 100, Y at level 200).

  Definition choose_left {E A} {x1 x2 : C.t E A} {v1 : A} (r1 : t x1 v1)
    : t (C.Choose x1 x2) v1 :=
    ChooseLeft r1.

  Definition choose_right {E A} {x1 x2 : C.t E A} {v2 : A} (r2 : t x2 v2)
    : t (C.Choose x1 x2) v2 :=
    ChooseRight r2.

  Definition join {E A B} {x : C.t E A} {y : C.t E B} {v_x : A} {v_y : B}
    (r_x : t x v_x) (r_y : t y v_y) : t (C.Join x y) (v_x, v_y) :=
    Join r_x r_y.
End Notations.

Module I.
  (** A run of an infinite computation. *)
  CoInductive t {E : Effect.t} : forall {A : Type}, C.I.t E A -> A -> Type :=
  | Ret : forall {A} (x : A), t (C.I.Ret (E := E) x) x
  | Call : forall (c : Effect.command E) (answer : Effect.answer E c),
    t (C.I.Call (E := E) c) answer
  | Let : forall {A B} {c_x : C.I.t E A} {x : A} {c_f : A -> C.I.t E B} {y : B},
    t c_x x -> t (c_f x) y -> t (C.I.Let c_x c_f) y
  | ChooseLeft : forall {A} {c_x1 c_x2 : C.I.t E A} {x1 : A},
    t c_x1 x1 -> t (C.I.Choose c_x1 c_x2) x1
  | ChooseRight : forall {A} {c_x1 c_x2 : C.I.t E A} {x2 : A},
    t c_x2 x2 -> t (C.I.Choose c_x1 c_x2) x2
  | Join : forall {A B} {c_x : C.I.t E A} {x : A} {c_y : C.I.t E B} {y : B},
    t c_x x -> t c_y y -> t (C.I.Join c_x c_y) (x, y).

  Module Notations.
    Definition ret {E A} (v : A) : t (E := E) (C.I.Ret v) v :=
      Ret v.

    Definition call (E : Effect.t) (c : Effect.command E)
      (a : Effect.answer E c) : t (C.I.Call c) a :=
      Call c a.

    (** A nicer notation for `Let`. *)
    Notation "'rlet!' X 'in' Y" :=
      (Let X Y)
      (at level 200, X at level 100, Y at level 200).

    (** Let ignoring the unit answer. *)
    Notation "'rdo!' X 'in' Y" :=
      (Let (A := unit) X Y)
      (at level 200, X at level 100, Y at level 200).

    Definition choose_left {E A} {x1 x2 : C.I.t E A} {v1 : A} (r1 : t x1 v1)
      : t (C.I.Choose x1 x2) v1 :=
      ChooseLeft r1.

    Definition choose_right {E A} {x1 x2 : C.I.t E A} {v2 : A} (r2 : t x2 v2)
      : t (C.I.Choose x1 x2) v2 :=
      ChooseRight r2.

    Definition join {E A B} {x : C.I.t E A} {y : C.I.t E B} {v_x : A} {v_y : B}
      (r_x : t x v_x) (r_y : t y v_y) : t (C.I.Join x y) (v_x, v_y) :=
      Join r_x r_y.
  End Notations.

  Definition unfold {E A} {c_x : C.I.t E A} {v_x : A} (r_x : t c_x v_x)
    : t c_x v_x :=
    match r_x with
    | Ret v => Ret v
    | Call c a => Call c a
    | Let r_x r_y => Let r_x r_y
    | ChooseLeft r_x1 => ChooseLeft r_x1
    | ChooseRight r_x2 => ChooseRight r_x2
    | Join r_x r_y => Join r_x r_y
    end.

  Definition unfold_eq {E A} {c_x : C.I.t E A} {v_x : A} (r_x : t c_x v_x)
    : r_x = unfold r_x.
    destruct r_x; reflexivity.
  Defined.

  Module Eq.
    CoInductive t {E} : forall {A} {x1 x2 : C.I.t E A} {v1 v2 : A},
      Run.I.t x1 v1 -> Run.I.t x2 v2 -> Prop :=
    | Ret : forall A (v : A), t (Ret v) (Ret v)
    | Call : forall c a, t (Call c a) (Call c a)
    | Let : forall A B (c_x1 c_x2 : C.I.t E A) (v_x1 v_x2 : A)
      (c_f1 c_f2 : A -> C.I.t E B) (v_y1 v_y2 : B)
      (r_x1 : Run.I.t c_x1 v_x1) (r_x2 : Run.I.t c_x2 v_x2)
      (r_y1 : Run.I.t (c_f1 v_x1) v_y1) (r_y2 : Run.I.t (c_f2 v_x2) v_y2),
      t r_x1 r_x2 -> t r_y1 r_y2 -> t (Let r_x1 r_y1) (Let r_x2 r_y2)
    | ChooseLeft : forall A (c_x11 c_x12 c_x21 c_x22 : C.I.t E A)
      (v_x11 v_x12 : A)
      (r_x11 : Run.I.t c_x11 v_x11) (r_x12 : Run.I.t c_x12 v_x12),
      t r_x11 r_x12 ->
      t (ChooseLeft (c_x2 := c_x21) r_x11) (ChooseLeft (c_x2 := c_x22) r_x12)
    | ChooseRight : forall A (c_x11 c_x12 c_x21 c_x22 : C.I.t E A)
      (v_x21 v_x22 : A)
      (r_x21 : Run.I.t c_x21 v_x21) (r_x22 : Run.I.t c_x22 v_x22),
      t r_x21 r_x22 ->
      t (ChooseRight (c_x1 := c_x11) r_x21) (ChooseRight (c_x1 := c_x12) r_x22)
    | Join : forall A B (c_x1 c_x2 : C.I.t E A) (c_y1 c_y2 : C.I.t E B)
      (v_x1 v_x2 : A) (v_y1 v_y2 : B)
      (r_x1 : Run.I.t c_x1 v_x1) (r_x2 : Run.I.t c_x2 v_x2)
      (r_y1 : Run.I.t c_y1 v_y1) (r_y2 : Run.I.t c_y2 v_y2),
      t r_x1 r_x2 -> t r_y1 r_y2 -> t (Join r_x1 r_y1) (Join r_x2 r_y2).
  End Eq.

  (** A lift from the finite runs. *)
  Fixpoint lift {E A} {x : C.t E A} {v : A} (r : Run.t x v) : t (C.I.lift x) v.
    destruct r; simpl.
    - apply Ret.
    - apply Call.
    - eapply Let.
      + apply (lift _ _ _ _ r1).
      + apply (lift _ _ _ _ r2).
    - apply ChooseLeft.
      apply (lift _ _ _ _ r).
    - apply ChooseRight.
      apply (lift _ _ _ _ r).
    - apply Join.
      + apply (lift _ _ _ _ r1).
      + apply (lift _ _ _ _ r2).
  Defined.
End I.
