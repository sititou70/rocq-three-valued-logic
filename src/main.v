Inductive tern : Type :=
  | t_true : tern
  | t_unknown : tern
  | t_false : tern.

Definition and (t1 t2: tern): tern :=
  match t1 with
    | t_true => t2
    | t_unknown =>
      match t2 with
        | t_false => t_false
        | _ => t_unknown
      end
    | t_false => t_false
  end.
Notation "a && b" := (and a b).

Definition or (t1 t2: tern): tern :=
  match t1 with
    | t_true => t_true
    | t_unknown =>
      match t2 with
        | t_true => t_true
        | _ => t_unknown
      end
    | t_false => t2
  end.
Notation "a || b" := (or a b).

Definition not (t1: tern): tern :=
  match t1 with
    | t_true => t_false
    | t_unknown => t_unknown
    | t_false => t_true
  end.

Theorem true_iff:
  forall (a b: tern),
  (a = t_true <-> b = t_true) ->
  (a <> t_true <-> b <> t_true).
Proof.
  intros a b Htrue_iff.
  split; intros H1 H2; destruct a, b;
  try solve [
    auto
  ];
  try solve [
    destruct (proj1 Htrue_iff); auto
  ];
  try solve [
    destruct (proj2 Htrue_iff); auto
  ].
Qed.

Theorem main:
  forall (a b c d: tern),
  a && c <> t_true ->
  b && d <> t_true ->
  (a || b) && (c || d) = t_true
  <->
  (a && d) || (c && b) = t_true.
Proof.
  intros a b c d H1 H2.
  split;
  intros H;
  destruct a, b, c, d;
  try solve [
    auto
  ];
  try solve [
    destruct H1;
    auto
  ];
  try solve [
    destruct H2;
    auto
  ].
Qed.
