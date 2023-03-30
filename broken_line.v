(* Make a broken line trajectory between points respecting a vertical
  cell decomposition. *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.

From cellDecomposition Require Import math_comp_complements points_and_edges
  cells cells_alg1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section two_adjacent_cells.

Variable R : realFieldType.

Notation pt := (pt R).
Notation edge := (edge R).
Notation cell := (cell R).
Notation dummy_pt := (dummy_pt R).
Notation dummy_edge := (dummy_edge R).
Notation dummy_cell := (dummy_cell R).

Record vert_edge :=
 { ve_x : R; ve_top : R; ve_bot : R}.

Definition vert_edge_eqb (v1 v2 : vert_edge) :=
  let: Build_vert_edge v1x v1t v1b := v1 in
  let: Build_vert_edge v2x v2t v2b := v2 in
  (v1x == v2x) && (v1t == v2t) && (v1b == v2b).

Lemma vert_edge_eqP : Equality.axiom vert_edge_eqb.
Proof.
move=> [v1x v1t v1b][v2x v2t v2b] /=.
have [/eqP <- | /eqP xn] := boolP (v1x == v2x).
  have [/eqP <- | /eqP tn] := boolP (v1t == v2t).
    have [/eqP <- | /eqP bn] := boolP (v1b == v2b).
      by apply: ReflectT.
    by apply: ReflectF => [] [].
  by apply: ReflectF => [] [].
by apply: ReflectF => [] [].
Qed.

Canonical vert_edge_eqType := EqType vert_edge (EqMixin vert_edge_eqP).

Definition vert_edge_pred (ve : vert_edge) : {pred pt} :=
  [pred p | (p_x p == ve_x ve) && (ve_bot ve < p_y p < ve_top ve)].

Coercion vert_edge_pred : vert_edge >-> pred_sort.

Fixpoint seq_to_intervals_aux [A : Type] (a : A) (s : seq A) :=
match s with
| nil => nil
| b :: tl => (a, b) :: seq_to_intervals_aux b tl
end.

Definition seq_to_intervals [A : Type] (s : seq A) :=
match s with
  nil => nil
| a :: tl => seq_to_intervals_aux a tl
end.

Lemma seq_to_intervals_aux_rcons [A : Type] (s : seq A) c a b :
 seq_to_intervals_aux c (rcons (rcons s a) b) = 
 rcons (seq_to_intervals_aux c (rcons s a)) (a, b).
Proof. by elim: s a b c => [ | d s Ih] //= a b c; rewrite Ih. Qed.

Lemma seq_to_intervals_rcons [A : Type] (s : seq A) a b :
 seq_to_intervals (rcons (rcons s a) b) =
 rcons (seq_to_intervals (rcons s a)) (a, b).
Proof.
by case: s => [ | c s] //=; rewrite seq_to_intervals_aux_rcons.
Qed.

Lemma seq_to_intervals_rev [A : Type] (s : seq A) :
  seq_to_intervals (rev s) = rev [seq (p.2, p.1) | p <- seq_to_intervals s].
Proof.
move: s => [ | a tl] //.
elim: tl a => [ | b tl Ih] //= a.
rewrite 2!rev_cons seq_to_intervals_rcons. 
by rewrite -rev_cons Ih -rev_cons.
Qed.

(* This returns the vertical edges that represent safe passage points
  out of a cell, in the left direction. *)
Definition cell_safe_exits_left (c : cell) : seq vert_edge :=
  let lx := p_x (head dummy_pt (left_pts c)) in
  map (fun p => Build_vert_edge lx (p_y p.1) (p_y p.2)) 
   (seq_to_intervals (left_pts c)).

(* This lemma plays the role of a test, to check that the order of
  bottom and top of the vertical edge has been programmed correctly. *)
Lemma cell_safe_exits_left_top_bot c :
  closed_cell_side_limit_ok c ->
  forall ve, ve \in cell_safe_exits_left c -> ve_bot ve < ve_top ve.
Proof.
rewrite /cell_safe_exits_left.
move=> /andP[] + /andP[] /allP + /andP[] + _.
case : (left_pts c) => [// | a tl] /= _.
elim : tl a => [ | b tl Ih] a //= samex /andP[] cmp sorted.
move=> ve; rewrite inE => /orP[/eqP -> | ] //=.
rewrite (eqP (samex a _)); last by rewrite inE eqxx.
rewrite -(eqP (samex b _)); last by rewrite 2!inE eqxx orbT.
by apply: Ih=> //; move=> x xin; apply: samex; rewrite inE xin orbT.
Qed.

Definition cell_safe_exits_right (c : cell) : seq vert_edge :=
  let lx := p_x (head dummy_pt (right_pts c)) in
  map (fun p => Build_vert_edge lx (p_y p.1) (p_y p.2)) 
   (seq_to_intervals (rev (right_pts c))).

(* This lemma plays is symmetric to the one on cell_safe_exits_left,
  but we need to see how to handle sorting and reversing lists. *)
Lemma cell_safe_exits_right_top_bot c :
  closed_cell_side_limit_ok c ->
  forall ve, ve \in cell_safe_exits_right c -> ve_bot ve < ve_top ve.
Proof.
rewrite /cell_safe_exits_right.
move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
move=> /andP[] + /andP[] /allP + /andP[] + _.
elim/last_ind : (right_pts c) => [| prefix a _] //= _.
elim/last_ind : prefix a => [ | prefix b Ih] a //= samex hs.
move=> ve.
move: (hs); rewrite [rcons _ _](_ : _ = prefix ++ [:: b; a]); last first.
  by rewrite -2!cats1 -!catA.
rewrite map_cat=> /sorted_catW => /andP[] _ /= /andP[] cmp _.
rewrite rev_cat /= inE=> /orP[/eqP -> | ] //=.
rewrite -[seq_to_intervals_aux _ _]/(seq_to_intervals (b :: rev prefix)).
rewrite -rev_rcons.
rewrite [p_x _](_ : _ = p_x (head dummy_pt (rcons prefix b))); last first.
  by case pfq : prefix => [ | d prefix'].
move=>/Ih; apply.
  move=> x xin; rewrite (eqP (samex _ _)); last first.
    by rewrite mem_rcons inE xin orbT.
  by case pfq : prefix => [ | d prefix'].
by move: hs; rewrite -cats1 map_cat=> /sorted_catW /andP[].
Qed.

Definition vert_edge_midpoint (ve : vert_edge) : pt :=
  {|p_x := ve_x ve; p_y := (ve_top ve + ve_bot ve) / 2%R|}.

Definition lr_connected (c1 c2 : cell) : bool :=
  [seq v | v <- cell_safe_exits_right c1 & v \in cell_safe_exits_left c2] !=
  [::].

Definition bi_connected c1 c2 :=
  lr_connected c1 c2 || lr_connected c2 c1.

Definition dummy_vert_edge :=
  {| ve_x := 0; ve_top := 0; ve_bot := 0|}.

(* In the first naive version, we assume there is only one common
  vertical edge between two cells.  This maybe wrong if events can be
  reduced to a single point. *)
Definition lr_door (c1 c2 : cell) :=
  head dummy_vert_edge
     [seq x | x <- cell_safe_exits_right c1 &
          x \in cell_safe_exits_left c2].

(* Construct a path between p1 and p2, assuming p1 is in the interior
  c1 and p2 in the interior of c2, c1 and c2 are lr_connected and
  respecting the fact that the
  only door from c1 to c2 is the common vertical edge. *)
Definition lr_connected_path (c1 c2 : cell) (p1 p2 : pt) :
  seq (pt * pt) :=
  [:: (p1, vert_edge_midpoint (lr_door c1 c2));
      (vert_edge_midpoint (lr_door c1 c2), p2)].

(* A first approximation of a path between two points is a path between
  cells.  This can be defined using the path function of mathcomp. *)

Definition connected_cells (c : cell) (s : seq cell) :=
  path bi_connected c s.

(* When building a path from c1 to c3 through c2, an easy case is when
   lr_connected c1 c2 and lr_connected c2 c3, or in the opposite direction
   lr_connected c3 c2 and lr_connected c2 c1.   Things are less pleasant
   if lr_connected c1 c2 and lr_connected c3 c2.  In this case, we need
   to exhibit a point inside c2 to move away from the vertical boundary,
   because points on the vertical boundary that are not part of the
   common vertical edges are likely to be collision points with some
   obstacle. *)

(* To produce a safe point inside a cell, we can take the point in the middle
  defined. *)

Definition midpoint (p1 p2 : pt) : pt :=
 {| p_x := (p_x p1 + p_x p2) / 2; p_y := (p_y p1 + p_y p2) / 2|}.

Definition cell_center (c : cell) :=
  midpoint
    (midpoint (last dummy_pt (left_pts c)) (head dummy_pt (right_pts c)))
    (midpoint (head dummy_pt (left_pts c)) (last dummy_pt (right_pts c))).

(* For a path of the form : c1 c2   cn-1 cn, we want to construct a path
  from the midpoint of the door from c1 to c2 to the midpoint of the door
  from cn-1 to cn.  The base case is when there are only two cells in
  the sequence, because in this case the two doors are the same.
  --- doors are vertical edges.
  Because the base case happens when there are two cells, we consider
  a function with 3 arguments, where two cells are the first two of the path. *)
Fixpoint connected_cells_path (c1 c2 : cell) (tl : seq cell) :=
  match tl with
  | nil => nil
  | c3 :: tl' =>
    let tail_path := connected_cells_path c2 c3 tl' in
    if lr_connected c1 c2 && lr_connected c2 c3 then
       (vert_edge_midpoint (lr_door c1 c2),
           vert_edge_midpoint (lr_door c2 c3)) ::
       tail_path else
    if lr_connected c3 c2 && lr_connected c2 c1 then
       (vert_edge_midpoint (lr_door c2 c1),
           vert_edge_midpoint (lr_door c3 c2)) ::
       tail_path else
    if lr_connected c1 c2 (* we assume lr_connected c3 c2 *) then
       [:: (vert_edge_midpoint (lr_door c1 c2), cell_center c2),
           (cell_center c2, vert_edge_midpoint (lr_door c3 c2)) &
           tail_path] else
    [:: (vert_edge_midpoint (lr_door c2 c1), cell_center c2),
        (cell_center c2, vert_edge_midpoint (lr_door c2 c3)) &
        tail_path]
  end.

Definition point_cell (p : pt) (s : seq cell) : option cell :=
  match [seq c | c <- s & strict_inside_closed p c] with
  | nil => None
  | a :: _ => Some a
  end.
