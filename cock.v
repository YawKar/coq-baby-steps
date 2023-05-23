From Coq Require Import Arith Bool.

(* Check shows the type of an expression *)
Check 3.
Check 3 + 3.
Check true.
Check (true && false).

(* Eval compute in EXPR shows the result of EXPR *)
Eval compute in 3 + 4.
Eval compute in (true && false).
Eval compute in (3 + 4).
Eval compute in (3+3*3).
Eval compute in 1.
Eval compute in (1).
Eval compute in (1, 2, 3, 4).
Eval compute in (1 * 2, 2 + 2, 3).

(* Print shows the definition of an argument *)
Print nat.
Check nat.
(* Fail ANYTHING checks that ANYTHING fails, otherwise fails *)
Fail Check print.

Print bool.

Inductive week_day: Set :=
| Monday: week_day
| Tuesday: week_day
| Wednesday: week_day
| Thursday: week_day
| Friday: week_day
| Saturday: week_day
| Sunday: week_day.

Print week_day.
Check Monday.

Definition return_monday : week_day := Monday.

Eval compute in return_monday.

Definition add_one (x: nat) : nat := x + 1.
Definition succ (x: nat) : nat := add_one x.

Eval compute in succ 5.
Eval compute in add_one 5.

Definition is_monday (wd: week_day) : bool :=
  match wd with
  | Monday => true
  | _ => false
  end.

Check is_monday.
Print is_monday.
Eval compute in is_monday Tuesday.
Eval compute in is_monday Monday.

Search (bool -> bool).

Search (nat -> nat).

Eval compute in Nat.sqrt 625.

Inductive week_day_list :=
| Nil: week_day_list
| Cons: week_day -> (week_day_list -> week_day_list).

Eval compute in Nil.
Eval compute in (Cons Tuesday (Cons Monday Nil)).
Eval compute in (Cons Tuesday).

Check Cons Tuesday.
Check Cons Tuesday Nil.

Definition tuesday_start := Cons Tuesday.
Eval compute in tuesday_start Nil.
Eval compute in tuesday_start (Cons Monday Nil).
Eval compute in tuesday_start (tuesday_start Nil).

Definition head (list : week_day_list) (default : week_day) : week_day :=
  match list with
  | Nil => default
  | Cons h _ => h
  end.

Eval compute in head (tuesday_start Nil) Monday.
Eval compute in head Nil Friday.

Notation "[ ]" := Nil.
Notation "[ w ]" := (Cons w Nil).
Notation "[ w1 ; w2 ; .. ; wn ]" := (Cons w1 (Cons w2 .. (Cons wn Nil) .. )).

Definition work_week := [Monday; Tuesday; Wednesday; Thursday; Friday].

Definition eq_wd (w1 w2 : week_day) : bool :=
  match (w1, w2) with
  | (Monday, Monday) => true
  | (Tuesday, Tuesday) => true
  | (Wednesday, Wednesday) => true
  | (Thursday, Thursday) => true
  | (Friday, Friday) => true
  | (Saturday, Saturday) => true
  | (Sunday, Sunday) => true
  | _ => false
  end.

Eval compute in eq_wd Monday Tuesday.
Eval compute in eq_wd Monday Monday.

Fixpoint length (l : week_day_list) : nat :=
  match l with
  | [] => 0
  | Cons w ws => (length ws) + 1
  end.

Eval compute in (length work_week).

Fixpoint is_a_member (w : week_day) (l : week_day_list) : bool :=
  match l with
  | [] => false
  | Cons w' ws => eq_wd w w' || is_a_member w ws
  end.















