(** Semantic of the comutations using traces. *)
Require C.
Require Run.

Inductive t (E : Effect.t) : Type :=
| Ret : t E
| Call : forall c, Effect.answer E c -> t E
| Let : t E -> t E -> t E
| ChooseLeft : t E -> t E
| ChooseRight : t E -> t E
| Join : t E -> t E -> t E.
Arguments Ret {E}.
Arguments Call {E} _ _.
Arguments Let {E} _ _.
Arguments ChooseLeft {E} _.
Arguments ChooseRight {E} _.
Arguments Join {E} _ _.

Module Notations.
  Definition ret {E} : t E :=
    Ret.

  Definition call (E : Effect.t) (c : Effect.command E) (a : Effect.answer E c)
    : t E :=
    Call c a.

  (** A nicer notation for `Let`. *)
  Notation "'tlet!' X 'in' Y" :=
    (Let X Y)
    (at level 200, X at level 100, Y at level 200).

  Definition choose_left {E} (tr : t E) : t E :=
    ChooseLeft tr.

  Definition choose_right {E} (tr : t E) : t E :=
    ChooseRight tr.

  Definition join {E} (tr_x tr_y : t E) : t E :=
    Join tr_x tr_y.
End Notations.

Module Valid.
  Inductive t {E} : forall {A}, C.t E A -> Trace.t E -> A -> Type :=
  | Ret : forall A (v : A), t (C.Ret A v) Trace.Ret v
  | Call : forall c (a : Effect.answer E c), t (C.Call c) (Trace.Call c a) a
  | Let : forall A B (x : C.t E A) (f : A -> C.t E B) (t_x t_y : Trace.t E)
    (v_x : A) (v_y : B),
    t x t_x v_x -> t (f v_x) t_y v_y ->
    t (C.Let _ _ x f) (Trace.Let t_x t_y) v_y
  | ChooseLeft : forall A (x1 x2 : C.t E A) (t_x1 : Trace.t E) (v_x1 : A),
    t x1 t_x1 v_x1 -> t (C.Choose _ x1 x2) (Trace.ChooseLeft t_x1) v_x1
  | ChooseRight : forall A (x1 x2 : C.t E A) (t_x2 : Trace.t E) (v_x2 : A),
    t x2 t_x2 v_x2 -> t (C.Choose _ x1 x2) (Trace.ChooseRight t_x2) v_x2
  | Join : forall A B (x : C.t E A) (y : C.t E B) (t_x t_y : Trace.t E)
    (v_x : A) (v_y : B),
    t x t_x v_x -> t y t_y v_y ->
    t (C.Join _ _ x y) (Trace.Join t_x t_y) (v_x, v_y).
End Valid.

Fixpoint of_run {E A} {x : C.t E A} {v_x : A} (r_x : Run.t x v_x)
  : {t_x : Trace.t E & Valid.t x t_x v_x}.
  destruct r_x.
  - exists Trace.Ret.
    apply Valid.Ret.
  - exists (Trace.Call c a).
    apply Valid.Call.
  - destruct (of_run _ _ _ _ r_x1) as [t_x H_x].
    destruct (of_run _ _ _ _ r_x2) as [t_y H_y].
    exists (Trace.Let t_x t_y).
    now apply Valid.Let with (v_x := x).
  - destruct (of_run _ _ _ _ r_x) as [t_x1 H_x1].
    exists (Trace.ChooseLeft t_x1).
    now apply Valid.ChooseLeft.
  - destruct (of_run _ _ _ _ r_x) as [t_x2 H_x2].
    exists (Trace.ChooseRight t_x2).
    now apply Valid.ChooseRight.
  - destruct (of_run _ _ _ _ r_x1) as [t_x H_x].
    destruct (of_run _ _ _ _ r_x2) as [t_y H_y].
    exists (Trace.Join t_x t_y).
    now apply Valid.Join.
Defined.

Fixpoint to_run {E A} {x : C.t E A} {t_x : Trace.t E} {v_x : A}
  (H : Valid.t x t_x v_x) : Run.t x v_x.
  destruct H.
  - apply Run.Ret.
  - apply Run.Call.
  - eapply Run.Let.
    + eapply to_run.
      apply H.
    + eapply to_run.
      apply H0.
  - apply Run.ChooseLeft.
    eapply to_run.
    apply H.
  - apply Run.ChooseRight.
    eapply to_run.
    apply H.
  - apply Run.Join.
    + eapply to_run.
      apply H.
    + eapply to_run.
      apply H0.
Defined.

Fixpoint of_to_run {E A} {x : C.t E A} {t_x : Trace.t E} {v_x : A}
  (H : Valid.t x t_x v_x) : of_run (to_run H) = existT _ t_x H.
  destruct H; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (of_to_run _ _ _ _ _ H).
    rewrite (of_to_run _ _ _ _ _ H0).
    reflexivity.
  - rewrite (of_to_run _ _ _ _ _ H).
    reflexivity.
  - rewrite (of_to_run _ _ _ _ _ H).
    reflexivity.
  - rewrite (of_to_run _ _ _ _ _ H).
    rewrite (of_to_run _ _ _ _ _ H0).
    reflexivity.
Qed.

Fixpoint to_of_run {E A} {x : C.t E A} {v_x : A} (r_x : Run.t x v_x)
  : (let (_, H) := of_run r_x in to_run H) = r_x.
  destruct r_x; simpl.
  - reflexivity.
  - reflexivity.
  - assert (H1 := to_of_run _ _ _ _ r_x1).
    destruct (of_run r_x1) as [t_x1 H_x1].
    assert (H2 := to_of_run _ _ _ _ r_x2).
    destruct (of_run r_x2) as [t_x2 H_x2].
    simpl.
    now rewrite H1; rewrite H2.
  - assert (H := to_of_run _ _ _ _ r_x).
    destruct (of_run r_x) as [t_x H_x].
    simpl.
    now rewrite H.
  - assert (H := to_of_run _ _ _ _ r_x).
    destruct (of_run r_x) as [t_x H_x].
    simpl.
    now rewrite H.
  - assert (H1 := to_of_run _ _ _ _ r_x1).
    destruct (of_run r_x1) as [t_x1 H_x1].
    assert (H2 := to_of_run _ _ _ _ r_x2).
    destruct (of_run r_x2) as [t_x2 H_x2].
    simpl.
    now rewrite H1; rewrite H2.
Qed.

Module I.
  CoInductive t (E : Effect.t) : Type :=
  | Ret : t E
  | Call : forall c, Effect.answer E c -> t E
  | Let : t E -> t E -> t E
  | ChooseLeft : t E -> t E
  | ChooseRight : t E -> t E
  | Join : t E -> t E -> t E.
  Arguments Ret {E}.
  Arguments Call {E} _ _.
  Arguments Let {E} _ _.
  Arguments ChooseLeft {E} _.
  Arguments ChooseRight {E} _.
  Arguments Join {E} _ _.

  Module Notations.
    Definition ret {E} : t E :=
      Ret.

    Definition call (E : Effect.t) (c : Effect.command E)
      (a : Effect.answer E c) : t E :=
      Call c a.

    (** A nicer notation for `Let`. *)
    Notation "'tilet!' X 'in' Y" :=
      (Let X Y)
      (at level 200, X at level 100, Y at level 200).

    Definition choose_left {E} (tr : t E) : t E :=
      ChooseLeft tr.

    Definition choose_right {E} (tr : t E) : t E :=
      ChooseRight tr.

    Definition join {E} (tr_x tr_y : t E) : t E :=
      Join tr_x tr_y.
  End Notations.

  Definition unfold {E} (t : Trace.I.t E) : Trace.I.t E :=
    match t with
    | Ret => Ret
    | Call c a => Call c a
    | Let t_x t_f => Let t_x t_f
    | ChooseLeft t => ChooseLeft t
    | ChooseRight t => ChooseRight t
    | Join t_x t_y => Join t_x t_y
    end.

  Definition unfold_eq {E} (t : Trace.I.t E) : t = unfold t.
    destruct t; reflexivity.
  Defined.

  Module Eq.
    CoInductive t {E} : Trace.I.t E -> Trace.I.t E -> Prop :=
    | Ret : t Ret Ret
    | Call : forall c a, t (Call c a) (Call c a)
    | Let : forall t_x1 t_x2 t_f1 t_f2, t t_x1 t_x2 -> t t_f1 t_f2 ->
      t (Let t_x1 t_f1) (Let t_x2 t_f2)
    | ChooseLeft : forall t1 t2, t t1 t2 ->
      t (ChooseLeft t1) (ChooseLeft t2)
    | ChooseRight : forall t1 t2, t t1 t2 ->
      t (ChooseRight t1) (ChooseRight t2)
    | Join : forall t_x1 t_x2 t_y1 t_y2, t t_x1 t_x2 -> t t_y1 t_y2 ->
      t (Join t_x1 t_y1) (Join t_x2 t_y2).
  End Eq.

  Module Valid.
    CoInductive t {E} : forall {A}, C.I.t E A -> Trace.I.t E -> A -> Type :=
    | Ret : forall A (v : A), t (C.I.Ret A v) Trace.I.Ret v
    | Call : forall c (a : Effect.answer E c),
      t (C.I.Call c) (Trace.I.Call c a) a
    | Let : forall A B (x : C.I.t E A) (f : A -> C.I.t E B)
      (t_x t_y : Trace.I.t E) (v_x : A) (v_y : B),
      t x t_x v_x -> t (f v_x) t_y v_y ->
      t (C.I.Let _ _ x f) (Trace.I.Let t_x t_y) v_y
    | ChooseLeft : forall A (x1 x2 : C.I.t E A) (t_x1 : Trace.I.t E) (v_x1 : A),
      t x1 t_x1 v_x1 -> t (C.I.Choose _ x1 x2) (Trace.I.ChooseLeft t_x1) v_x1
    | ChooseRight : forall A (x1 x2 : C.I.t E A) (t_x2 : Trace.I.t E) (v_x2 : A),
      t x2 t_x2 v_x2 -> t (C.I.Choose _ x1 x2) (Trace.I.ChooseRight t_x2) v_x2
    | Join : forall A B (x : C.I.t E A) (y : C.I.t E B) (t_x t_y : Trace.I.t E)
      (v_x : A) (v_y : B),
      t x t_x v_x -> t y t_y v_y ->
      t (C.I.Join _ _ x y) (Trace.I.Join t_x t_y) (v_x, v_y).
    Arguments Ret {E A} _.
    Arguments Call {E} _ _.
    Arguments Let {E A B x f t_x t_y v_x v_y} _ _.
    Arguments ChooseLeft {E A x1 x2 t_x1 v_x1} _.
    Arguments ChooseRight {E A x1 x2 t_x2 v_x2} _.
    Arguments Join {E A B x y t_x t_y v_x v_y} _ _.

    Definition unfold {E A} {x : C.I.t E A} {t : Trace.I.t E} {v : A}
      (H : Valid.t x t v) : Valid.t x t v :=
      match H with
      | Ret v => Ret v
      | Call c a => Call c a
      | Let H_x H_f => Let H_x H_f
      | ChooseLeft H_x1 => ChooseLeft H_x1
      | ChooseRight H_x2 => ChooseRight H_x2
      | Join H_x H_y => Join H_x H_y
      end.

    Definition unfold_eq {E A} {x : C.I.t E A} {t : Trace.I.t E} {v : A}
      (H : Valid.t x t v) : H = unfold H.
      destruct H; reflexivity.
    Defined.
  End Valid.

  CoFixpoint trace_of_run {E A} {x : C.I.t E A} {v_x : A} (r_x : Run.I.t x v_x)
    : Trace.I.t E.
    destruct r_x.
    - exact Trace.I.Ret.
    - exact (Trace.I.Call c answer).
    - exact (Trace.I.Let (trace_of_run _ _ _ _ r_x1) (trace_of_run _ _ _ _ r_x2)).
    - exact (Trace.I.ChooseLeft (trace_of_run _ _ _ _ r_x)).
    - exact (Trace.I.ChooseRight (trace_of_run _ _ _ _ r_x)).
    - exact (Trace.I.Join
        (trace_of_run _ _ _ _ r_x1) (trace_of_run _ _ _ _ r_x2)).
  Defined.

  CoFixpoint valid_of_run {E A} {x : C.I.t E A} {v_x : A} (r_x : Run.I.t x v_x)
    : Valid.t x (trace_of_run r_x) v_x.
    rewrite (Trace.I.unfold_eq (trace_of_run _)).
    destruct r_x; simpl.
    - apply Valid.Ret.
    - apply Valid.Call.
    - eapply Valid.Let; apply valid_of_run.
    - apply Valid.ChooseLeft; apply valid_of_run.
    - apply Valid.ChooseRight; apply valid_of_run.
    - apply Valid.Join; apply valid_of_run.
  Defined.

  CoFixpoint to_run {E A} {x : C.I.t E A} {t_x : Trace.I.t E} {v_x : A}
    (H : Valid.t x t_x v_x) : Run.I.t x v_x.
    destruct H.
    - apply Run.I.Ret.
    - apply Run.I.Call.
    - eapply Run.I.Let.
      + eapply to_run.
        apply H.
      + eapply to_run.
        apply H0.
    - apply Run.I.ChooseLeft.
      eapply to_run.
      apply H.
    - apply Run.I.ChooseRight.
      eapply to_run.
      apply H.
    - apply Run.I.Join.
      + eapply to_run.
        apply H.
      + eapply to_run.
        apply H0.
  Defined.

  CoFixpoint trace_of_to_run {E A} {x : C.I.t E A} {t_x : Trace.I.t E} {v_x : A}
    (H : Valid.t x t_x v_x) : Trace.I.Eq.t (trace_of_run (to_run H)) t_x.
    rewrite (Trace.I.unfold_eq (trace_of_run _)).
    destruct H; simpl.
    - apply Trace.I.Eq.Ret.
    - apply Trace.I.Eq.Call.
    - apply Trace.I.Eq.Let; apply trace_of_to_run.
    - apply Trace.I.Eq.ChooseLeft; apply trace_of_to_run.
    - apply Trace.I.Eq.ChooseRight; apply trace_of_to_run.
    - apply Trace.I.Eq.Join; apply trace_of_to_run.
  Qed.

  CoFixpoint to_of_run {E A} {x : C.I.t E A} {v : A} (r : Run.I.t x v)
    : Run.I.Eq.t (to_run (valid_of_run r)) r.
    rewrite (Run.I.unfold_eq (to_run _)).
    destruct r; simpl.
    - apply Run.I.Eq.Ret.
    - apply Run.I.Eq.Call.
    - apply Run.I.Eq.Let; apply to_of_run.
    - apply Run.I.Eq.ChooseLeft; apply to_of_run.
    - apply Run.I.Eq.ChooseRight; apply to_of_run.
    - apply Run.I.Eq.Join; apply to_of_run.
  Qed.
End I.
