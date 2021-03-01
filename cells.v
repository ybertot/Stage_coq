From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section with_rcf.

Variable R : rcfType.

Import GRing.Theory Num.Theory Num.ExtraDef.

Open Scope ring_scope.

Record pt := Bpt {p_x : R; p_y : R}.

Definition pt_eqb (a b : pt) : bool :=
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
     (a_x == b_x) && (a_y == b_y).

Lemma pt_eqP : Equality.axiom pt_eqb.
Proof.
move=> [a_x a_y] [b_x b_y] /=.
have [/eqP <- | /eqP anb] := boolP(a_x == b_x).
  have [/eqP <- | /eqP anb] := boolP(a_y == b_y).
    by apply: ReflectT.
  by apply: ReflectF=> [][].
by apply: ReflectF=> [][].
Qed.

Canonical pt_eqType := EqType pt (EqMixin pt_eqP).

Record edge := Bedge {left_pt : pt; right_pt : pt;
    _ : p_x left_pt < p_x right_pt}.

Definition edge_eqb (e1 e2 : edge) : bool :=
   let: Bedge a1 b1 p1 := e1 in
   let: Bedge a2 b2 p2 := e2 in
   (a1 == a2) && (b1 == b2).

Lemma edge_cond (e : edge) : p_x (left_pt e) < p_x (right_pt e).
Proof.  by move: e => [l r c]. Qed.
   
Lemma edge_eqP : Equality.axiom edge_eqb.
Proof.
move=> [a1 b1 p1] [a2 b2 p2] /=.
have [/eqP a1a2 | /eqP a1na2] := boolP(a1 == a2).
  have [/eqP b1b2 | /eqP b1nb2] := boolP(b1 == b2).
     move: p1 p2; rewrite -a1a2 -b1b2=> p1 p2.
     rewrite (eqtype.bool_irrelevance p1 p2).
     by apply: ReflectT.
   by apply: ReflectF=> [][].
by apply: ReflectF=>[][].
Qed.

Canonical edge_eqType := EqType edge (EqMixin edge_eqP).

Record cell := Bcell  {pts : list pt; edges : list edge}.

Definition cell_eqb (c1 c2 : cell) : bool :=
  let: Bcell pts1 edges1 := c1 in
  let: Bcell pts2 edges2 := c2 in
  (pts1 == pts2) && (edges1 == edges2).









