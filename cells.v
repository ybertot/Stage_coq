From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Section with_rcf.
Print archiType.
Variable R : archiType.*)

Import GRing.Theory Num.Theory Num.ExtraDef.

Open Scope ring_scope.

Record pt := Bpt {p_x : archiType; p_y : archiType}.

Definition pt_eqb (a b : pt) : bool :=
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
     (a_x == b_x) && (a_y == b_y).

Lemma pt_eqP : Equality.axiom pt_eqb.
Proof.
rewrite /Equality.axiom.
move=> [a_x a_y] [b_x b_y] /=.
have [/eqP <-|/eqP anb] := boolP(a_x == b_x).

  have [/eqP <- | /eqP anb] := boolP(a_y == b_y).
    by apply: ReflectT.
  by apply : ReflectF => [][].
by apply: ReflectF=> [][].
Qed.

Canonical pt_eqType := EqType pt (EqMixin pt_eqP).

Record edge := Bedge {left_pt : pt; right_pt : pt;
    _ : p_x left_pt <= p_x right_pt}.

Definition edge_eqb (e1 e2 : edge) : bool :=
   let: Bedge a1 b1 p1 := e1 in
   let: Bedge a2 b2 p2 := e2 in
   (a1 == a2) && (b1 == b2).

Lemma edge_cond (e : edge) : p_x (left_pt e) <= p_x (right_pt e).
Proof.  by move: e => [l r c]. Qed.
   
Lemma edge_eqP : Equality.axiom edge_eqb.
Proof.
move=> [a1 b1 p1] [a2 b2 p2] /=.
have [/eqP a1a2 | /eqP a1na2] := boolP(a1 == a2).
  have [/eqP b1b2 | /eqP b1nb2] := boolP(b1 == b2).
     move: p1 p2. rewrite -a1a2 -b1b2 => p1 p2.
     rewrite (eqtype.bool_irrelevance p1 p2).
     by apply: ReflectT.
   by apply: ReflectF=> [][].
by apply: ReflectF=>[][].
Qed.

Canonical edge_eqType := EqType edge (EqMixin edge_eqP).

Record cell := Bcell  {pts : list pt; edges : list edge}.

Definition cell_eqb (ca cb : cell) : bool :=
  let: Bcell ptsa edgesa := ca in
  let: Bcell ptsb edgesb := cb in
  (ptsa == ptsb) && (edgesa == edgesb).


Lemma cell_eqP : Equality.axiom cell_eqb.
Proof.
rewrite /Equality.axiom.
move => [ptsa edgesa] [ptsb edgesb] /=.
have [/eqP <-|/eqP anb] := boolP(ptsa == ptsb).
  have [/eqP <-|/eqP anb] := boolP(edgesa == edgesb).
    by apply:ReflectT.
  by apply : ReflectF => [][].
by apply: ReflectF=> [][].
Qed.

Record event := Bevent {point : pt; incoming : seq edge; outgoing : seq edge}.

(* As in insertion sort, the add_event function assumes that event are
  sorted in evs (lexicographically, first coordinate, then second coordinate
  of the point.  On the other hand, no effort is made to sort the various
  edges in each list.  *)
Fixpoint add_event (p : pt) (e : edge) (incoming : bool) (evs : seq event) :
  seq event :=
  match evs with
  | nil => if incoming then [:: Bevent p [:: e] [::]]
           else [:: Bevent p [::] [:: e]]
  | Bevent p1 i1 o1 as ev1 :: evs' =>
    if p == p1 then
      if incoming then Bevent p1 (e :: i1) o1 :: evs'
      else Bevent p1 i1 (e :: o1) :: evs' else
    if p_x p < p_x p1 then Bevent p [:: e] [::] :: evs else
    if (p_x p == p_x p1) && (p_y p < p_y p1) then
       Bevent p [:: e] [::] :: evs else
    ev1 :: add_event p e incoming evs'
  end.

(* We should be able to prove that the sequence of events produced by
  edges to events is sorted lexicographically on the coordinates of
  the points. *)
Fixpoint edges_to_events (s : seq edge) : seq event :=
  match s with
  | nil => nil
  | e :: s' =>
    add_event (left_pt e) e false
      (add_event (right_pt e) e true (edges_to_events s'))
  end.

(*returns true if e1 is under e2*)
Definition compare_incoming (e1 e2 : edge) : bool :=
  let: Bedge a1 b1 p1 := e1 in
  let: Bedge a2 b2 p2 := e2 in
  let: Bpt a1_x a1_y := a1 in
  let: Bpt b1_x b1_y := b1 in
  let: Bpt a2_x a2_y := a2 in
     (b1_x * a1_y - a1_x * b1_y - (a2_x * a1_y - a1_x * a2_y) + a2_x * b1_y - b1_x * a2_y)<=0.


Check @Bedge (Bpt 3%:Q 4%:Q) (Bpt 4%:Q 4%:Q) isT.

Compute compare_incoming  (@Bedge  (Bpt 3%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT) (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT ).


(*returns true if e1 is under e2*)
Definition compare_outgoing (e1 e2 : edge) : bool :=
  let: Bedge a1 b1 p1 := e1 in
  let: Bedge a2 b2 p2 := e2 in
  let: Bpt a1_x a1_y := a1 in
  let: Bpt b1_x b1_y := b1 in
  let: Bpt b2_x b2_y := b2 in
     (b2_x * b1_y - b1_x * b2_y - (a1_x * b1_y - b1_x * a1_y) + a1_x * b2_y - b2_x * a1_y)<=0.

Compute compare_outgoing (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 1%:Q) isT ) (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT).

Definition sort_incoming (incoming : seq edge) : seq edge :=
  sort compare_incoming incoming.
Definition sort_outgoing (outgoing : seq edge) : seq edge :=
  sort compare_outgoing outgoing.


Definition E1 : edge := (@Bedge  (Bpt 2%:Q 5%:Q) (Bpt 3%:Q 3%:Q) isT).

Definition E2 : edge := (@Bedge  (Bpt 3%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT).
Definition E3 : edge := (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT).
Definition sorted_inc := map left_pt (sort_incoming [:: E1; E2; E3]).
Eval lazy in sorted_inc. 


Definition E4 : edge := (@Bedge  (Bpt 2%:Q 3%:Q) (Bpt 4%:Q 6%:Q) isT).
Definition E5 : edge := (@Bedge  (Bpt 2%:Q 3%:Q) (Bpt 5%:Q 3%:Q) isT).
Definition E6 : edge := (@Bedge  (Bpt 2%:Q 3%:Q) (Bpt 4%:Q 3%:Q) isT).

Definition sorted_out := map right_pt (sort_outgoing [:: E4; E5; E6]).
Eval lazy in sorted_out. 


