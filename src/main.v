Inductive tern : Type :=
  | t_true : tern
  | t_unknown : tern
  | t_false : tern.

Definition eqb (t1 t2: tern): bool :=
  match t1, t2 with
    | t_true, t_true => true
    | t_true, t_unknown => false
    | t_true, t_false => false
    | t_unknown, t_true => false
    | t_unknown, t_unknown => true
    | t_unknown, t_false => false
    | t_false, t_true => false
    | t_false, t_unknown => false
    | t_false, t_false => true
  end.
Notation "a = b" := (eqb a b).

Definition and (t1 t2: tern): tern :=
  match t1 with
    | t_true => t2
    | t_unknown => if t2 = t_false then t_false else t_unknown
    | t_false => t_false
  end.
Notation "a && b" := (and a b).

Definition or (t1 t2: tern): tern :=
  match t1 with
    | t_true => t_true
    | t_unknown => if t2 = t_true then t_true else t_unknown
    | t_false => t2
  end.
Notation "a || b" := (or a b).

Definition not (t1: tern): tern :=
  match t1 with
    | t_true => t_false
    | t_unknown => t_unknown
    | t_false => t_true
  end.

Theorem main:
  forall (a b c d: tern),
  not (a && c) = t_true ->
  not (b && d) = t_true ->
  (a || b) && (c || d) = (d && a) || (c && b).
Proof.
  intros a b c d Hnac Hnbd.
  destruct a, b, c, d;
  try solve [
    auto
  ];
  try solve [
    inversion Hnac
  ];
  try solve [
    inversion Hnbd
  ].
Qed.
