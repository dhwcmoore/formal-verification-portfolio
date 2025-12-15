
From Coq Require Import Reals List String Recdef.
From Coq Require Import Lra.
Import ListNotations.
Open Scope R_scope.

(* === Definitions === *)

Record ClassBoundary := mkBoundary {
  lower : R;
  upper : R;
  category : string
}.

Definition ClassDomain := list ClassBoundary.

(* === Helper Functions === *)

Definition in_interval (x : R) (b : ClassBoundary) : Prop :=
  (lower b <= x < upper b)%R.

Definition adjacent (b1 b2 : ClassBoundary) : Prop :=
  (upper b1 = lower b2)%R.

Fixpoint dom_length (d : ClassDomain) : nat := List.length d.

Fixpoint sorted (dom : ClassDomain) : Prop :=
  match dom with
  | [] => True
  | b1 :: rest => match rest with
    | [] => True
    | b2 :: rest' => (lower b1 <= lower b2)%R /\ sorted rest
    end
  end.

Fixpoint no_gaps (dom : ClassDomain) : Prop :=
  match dom with
  | [] => True
  | b1 :: rest => match rest with
    | [] => True
    | b2 :: rest' => adjacent b1 b2 /\ no_gaps rest
    end
  end.

(* === Example === *)

Definition example_dom : ClassDomain :=
  [ mkBoundary 0 2 "A";
    mkBoundary 2 5 "B";
    mkBoundary 5 8 "C"
  ].

Example in_example : in_interval 3 (mkBoundary 1 5 "OK").
Proof.
  unfold in_interval; cbn.
  split; lra.
Qed.

Example ex_sorted : sorted example_dom.
Proof.
  unfold example_dom.
  cbn.
  repeat split; lra.
Qed.

Example ex_no_gaps : no_gaps example_dom.
Proof.
  unfold example_dom.
  cbn.
  repeat split; reflexivity.
Qed.
