From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.


Require Import generic_trajectories.
Require Import math_comp_complements points_and_edges events cells.
Require Import opening_cells cells_alg safe_cells.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section fix_num_type.

Variable R : realFieldType.

Variable plain_edge : Type.
Variable plain_Bedge : generic_trajectories.pt R ->
  generic_trajectories.pt R -> plain_edge.
Variable p_left_pt : plain_edge -> generic_trajectories.pt R.
Variable p_right_pt : plain_edge -> generic_trajectories.pt R.

Definition a_pt (p : generic_trajectories.pt R) :=
  {| points_and_edges.p_x := generic_trajectories.p_x _ p;
     points_and_edges.p_y := generic_trajectories.p_y _ p|}.

Lemma c_a_pt_x (p : generic_trajectories.pt R) :
  generic_trajectories.p_x _ p = p_x (a_pt p).
Proof. by case: p. Qed.

Lemma c_a_pt_y (p : generic_trajectories.pt R) :
  generic_trajectories.p_y _ p = p_y (a_pt p).
Proof. by case: p. Qed.

Lemma c_pt_eqb p1 p2 :
  generic_trajectories.pt_eqb R eq_op p1 p2 = (a_pt p1 == a_pt p2).
Proof. by move: p1 p2 => [] x1 y1 [] x2 y2. Qed.

Definition r_seq_pt (s1 : seq (generic_trajectories.pt R))
  (s2 : seq (pt R)) :=
  all2 (fun x y => a_pt x == y) s1 s2.

Definition r_edge (e1 : plain_edge) (e2 : edge R) :=
  (a_pt (p_left_pt e1) == left_pt e2) &&
  (a_pt (p_right_pt e1) == right_pt e2).

Definition r_seq_edge (s1 : seq plain_edge) (s2 : seq (edge R)) :=
  all2 (fun x y => r_edge x y) s1 s2.

Definition r_event (e1 : generic_trajectories.event R plain_edge)
  (e2 : event R) :=
  (a_pt (generic_trajectories.point _ _ e1) == point e2) &&
  r_seq_edge (generic_trajectories.outgoing _ _ e1) (outgoing e2).
  
Definition r_seq_event (s1 : seq (generic_trajectories.event R plain_edge))
  (s2 : seq (event R)) :=
  all2 (fun x y => r_event x y) s1 s2.

Lemma c_R_ltb (x y : R) :
  R_ltb _ eq_op le x y = (x < y).
Proof. by rewrite /R_ltb -lt_neqAle. Qed.

Lemma c_add_event (p : generic_trajectories.pt R) 
  (e1 : plain_edge) (e2 : edge R) (b : bool) s1 s2 :
  r_seq_event s1 s2 ->
  r_edge e1 e2 ->
  r_seq_event (generic_trajectories.add_event _ eq_op le plain_edge
     p e1 b s1) (add_event (a_pt p) e2 b s2).
Proof.
elim: s1 s2 => [ | ev1 evs1 Ih] [ | ev2 evs2] //= cndS cnd_edge.
  case: ifP => //= cnd1.
    by rewrite /r_event eqxx.
  by rewrite /r_event eqxx /= cnd_edge.
rewrite c_pt_eqb.
move: cndS=> /andP[] /andP[] /[dup] cnd_point /eqP -> cnd_out cnd_evs.
case: ifP => peq.
  case: ifP=> cnd_b //=.
    by rewrite cnd_evs andbT /r_event /= cnd_point cnd_out.
  by rewrite /r_event /= cnd_point cnd_edge cnd_out cnd_evs.
rewrite c_R_ltb.
rewrite -(eqP cnd_point) -c_a_pt_x.
case: ifP => cnd_x_p.
  case: ifP=> cnd_b /=.
    by rewrite /r_event /= eqxx cnd_point cnd_out cnd_evs.
  by rewrite /r_event /= eqxx cnd_edge cnd_point cnd_out cnd_evs.
case: ifP=> cnd_x_p'.
  move: cnd_x_p'; rewrite c_R_ltb => ->.
  case: ifP=> cnd_b.
    by rewrite /= /r_event /= eqxx cnd_point cnd_out cnd_evs.
  by rewrite /= /r_event /= eqxx cnd_edge cnd_point cnd_out cnd_evs.
move: cnd_x_p'; rewrite c_R_ltb => ->.
by rewrite /= /r_event cnd_point cnd_out Ih.
Qed.

Lemma c_edges_to_events (s1 : seq plain_edge) (s2 : seq (edge R)) :
  r_seq_edge s1 s2 ->
  r_seq_event 
    (generic_trajectories.edges_to_events R eq_op le plain_edge
        p_left_pt p_right_pt s1) (edges_to_events s2).
Proof.
elim: s1 s2 => [ | g1 s1 Ih][ | g2 s2] //=.
move=> /andP[] /[dup] cnd_g1 /andP[] /eqP <- /eqP <- cnd_s1.
apply: c_add_event=> //.
apply: c_add_event=> //.
by apply: Ih.
Qed.

Lemma no_dup_seq_aux_eq {A : eqType} (s : seq A) :
  no_dup_seq s = no_dup_seq_aux eq_op s.
Proof. by elim: s => [ | a s /= ->]. Qed.

Lemma c_no_dup_seq s1 s2 :
  r_seq_pt s1 s2 ->
  r_seq_pt (no_dup_seq_aux (generic_trajectories.pt_eqb R eq_op) s1)
  (no_dup_seq s2).
Proof.
elim: s1 s2=> [ | p1 s1 Ih] [ | p2 s2] //= /andP[] cnd_p cnd_s.
case: s1 s2 cnd_s Ih => [ | p3 s1] [ | p4 s2] //. 
  by move=> _ Ih /=; rewrite cnd_p.
rewrite /= => /andP[] cnd_p3 cnd_s Ih.
move: (Ih (p4 :: s2)); rewrite cnd_p3 cnd_s=> /(_ isT) {}Ih.
case: ifP=> [p1qp3 | p1np3].
  rewrite c_pt_eqb (eqP cnd_p) (eqP cnd_p3) in p1qp3.
  rewrite p1qp3.
  exact: Ih.
rewrite c_pt_eqb (eqP cnd_p) (eqP cnd_p3) in p1np3.
by rewrite p1np3 /= cnd_p Ih.
Qed.

Lemma c_valid_edge p1 p2 g1 g2 :
  r_edge g1 g2 -> a_pt p1 == p2 ->
  generic_trajectories.valid_edge R le plain_edge p_left_pt p_right_pt g1 p1 =
  valid_edge g2 p2.
Proof.
move=> /andP[] cnd_l cnd_r cnd_pt.
rewrite -(eqP cnd_pt).
rewrite /generic_trajectories.valid_edge /valid_edge /=.
by rewrite -(eqP cnd_l) -(eqP cnd_r) c_a_pt_x.
Qed.

Definition r_option_pt (p1 : option (generic_trajectories.pt R))
  (p2 : option (pt R)) :=
  match p1, p2 with
    None, None => true
  | Some p1, Some p2 => a_pt p1 == p2
  | _, _ => false
  end.

Lemma c_vertical_intersection_point p1 p2 g1 g2 :
  a_pt p1 == p2 ->
  r_edge g1 g2 ->
  r_option_pt
  (generic_trajectories.vertical_intersection_point R le +%R (fun x y => x - y)
   *%R (fun x y => x / y) plain_edge p_left_pt p_right_pt p1 g1)
  (vertical_intersection_point p2 g2).
Proof.
move=> cnd_p cnd_g.
rewrite /generic_trajectories.vertical_intersection_point
  /vertical_intersection_point.
rewrite (c_valid_edge cnd_g cnd_p).
case: ifP => // vg.
move: cnd_g=> /andP[] /eqP <- /eqP <-.
rewrite -(eqP cnd_p).
by rewrite !c_a_pt_x !c_a_pt_y /r_option_pt /=.
Qed.

Lemma c_pue_formula p1 a1 b1 p2 a2 b2 :
  a_pt p1 == p2 ->
  a_pt a1 == a2 ->
  a_pt b1 == b2 ->
  generic_trajectories.pue_formula R +%R (fun x y => x - y) *%R p1 a1 b1 =
  pue_formula p2 a2 b2.
Proof.
rewrite /generic_trajectories.pue_formula /pue_formula.
move=> /eqP <- /eqP <- /eqP <-.
by move: p1 a1 b1=> -[] x1 y1 [] x2 y2 [] x3 y3 /=.
Qed.

Lemma c_point_under_edge p1 g1 p2 g2 :
  a_pt p1 == p2 ->
  r_edge g1 g2 ->
  generic_trajectories.point_under_edge R le +%R (fun x y => x - y) *%R
  0 plain_edge p_left_pt p_right_pt p1 g1 =
  point_under_edge p2 g2.
Proof.
rewrite /generic_trajectories.point_under_edge /point_under_edge.
move=> qp /andP[] ql qr.
by rewrite (c_pue_formula qp ql qr).
Qed.

Lemma c_point_strictly_under_edge p1 g1 p2 g2 :
  a_pt p1 == p2 ->
  r_edge g1 g2 ->
  generic_trajectories.point_strictly_under_edge R eq_op le +%R
  (fun x y => x - y) *%R
  0 plain_edge p_left_pt p_right_pt p1 g1 =
  point_strictly_under_edge p2 g2.
Proof.
rewrite /generic_trajectories.point_strictly_under_edge.
rewrite /point_strictly_under_edge.
move=> qp /andP[] ql qr.
by rewrite (c_pue_formula qp ql qr) c_R_ltb.
Qed.

Lemma c_edge_below g1 g2 g3 g4 :
  r_edge g1 g3 ->
  r_edge g2 g4 ->
  generic_trajectories.edge_below R eq_op le +%R (fun x y => x - y) *%R 0
  plain_edge p_left_pt p_right_pt g1 g2 =
  edge_below g3 g4.
Proof.
move=> cnd_g1 cnd_g2; rewrite /generic_trajectories.edge_below /edge_below.
move: (cnd_g1)=> /andP[] cnd_g1l cnd_g1r.
move: (cnd_g2)=> /andP[] cnd_g2l cnd_g2r.
rewrite (c_point_under_edge cnd_g1l cnd_g2)
  (c_point_under_edge cnd_g1r cnd_g2).
by rewrite (c_point_strictly_under_edge cnd_g2l cnd_g1)
  (c_point_strictly_under_edge cnd_g2r cnd_g1).
Qed.

Definition r_cell (c1 : generic_trajectories.cell R plain_edge)
  (c2 : cell R) :=
  r_seq_pt (generic_trajectories.left_pts _ _ c1) (left_pts c2) &&
  r_seq_pt (generic_trajectories.right_pts _ _ c1) (right_pts c2) &&
  r_edge (generic_trajectories.low _ _ c1) (low c2) &&
  r_edge (generic_trajectories.high _ _ c1) (high c2).
  
Definition r_seq_cell (s1 : seq (generic_trajectories.cell R plain_edge))
  (s2 : seq (cell R)) :=
  all2 r_cell s1 s2.

Lemma c_contains_point p1 c1 p2 c2 :
  a_pt p1 == p2 ->
  r_cell c1 c2 ->
  generic_trajectories.contains_point R eq_op le +%R (fun x y => x - y)
   *%R 0 plain_edge p_left_pt p_right_pt p1 c1 =
  contains_point p2 c2.
Proof.
move=> cnd_p1 /andP[] /andP[] /andP[] _ _ cnd_l cnd_h.
rewrite /generic_trajectories.contains_point/contains_point.
rewrite (c_point_strictly_under_edge cnd_p1 cnd_l).
by rewrite (c_point_under_edge cnd_p1 cnd_h).
Qed.

Arguments no_dup_seq_aux : simpl never.
Arguments no_dup_seq : simpl never.

Lemma c_close_cell p1 p2 c1 c2 :
  a_pt p1 == p2 ->
  r_cell c1 c2 ->
  r_cell (generic_trajectories.close_cell R eq_op le +%R (fun x y => x - y)
     *%R (fun x y => x / y) plain_edge p_left_pt p_right_pt
    p1 c1) (close_cell p2 c2).
Proof.
move=> cnd_pt /[dup] cnd_c /andP[] /andP[] /andP[] cnd_ls cnd_rs cnd_l cnd_h.
rewrite /generic_trajectories.close_cell /close_cell.
have := (c_vertical_intersection_point cnd_pt cnd_l).
rewrite /r_option_pt.
case: generic_trajectories.vertical_intersection_point => [p | ]; last first.
  by case: vertical_intersection_point => [ p' | ].
case: vertical_intersection_point => [ p' | ] //.
have := (c_vertical_intersection_point cnd_pt cnd_h).
rewrite /r_option_pt.
case: generic_trajectories.vertical_intersection_point => [p3 | ]; last first.
  by case: vertical_intersection_point => [ p3' | ].
case: vertical_intersection_point => [ p3' | ] //.
rewrite /r_cell /=.
move=> /eqP <- /eqP <-.
rewrite cnd_ls -(eqP cnd_pt) /= cnd_l cnd_h !andbT.
by apply: c_no_dup_seq; rewrite /= !eqxx.
Qed.

Lemma c_closing_cells p1 p2 s1 s2 :
  a_pt p1 == p2 ->
  r_seq_cell s1 s2 ->
  r_seq_cell (generic_trajectories.closing_cells R eq_op le +%R (fun x y => x - y)
     *%R (fun x y => x / y) plain_edge p_left_pt p_right_pt
     p1 s1)
   (closing_cells p2 s2). 
Proof.
move=> cnd_p1.
elim: s1 s2 => [ | c1 s1 Ih] [ | c2 s2] //= /andP[] cnd_c1 cnd_s1.
by rewrite (c_close_cell cnd_p1 cnd_c1) Ih.
Qed.

Lemma c_pvert_y p1 p2 g1 g2 :
  a_pt p1 == p2 ->
  r_edge g1 g2 ->
  generic_trajectories.pvert_y R le +%R (fun x y => x - y) *%R 
  (fun x y => x / y) 0 plain_edge p_left_pt p_right_pt p1 g1 =
  pvert_y p2 g2.
Proof.
move=> cnd_p cnd_g.
rewrite /generic_trajectories.pvert_y /pvert_y.
have := (c_vertical_intersection_point cnd_p cnd_g).
case: generic_trajectories.vertical_intersection_point => [p' | ].
  rewrite /r_option_pt.
  case: vertical_intersection_point=> [p'2 /eqP <- | ]; last by [].
  by apply: c_a_pt_y.
rewrite /r_option_pt.
by case: vertical_intersection_point.
Qed.

Definition r_prod_seq_cell_cell (p1 : seq (generic_trajectories.cell R plain_edge) * generic_trajectories.cell R plain_edge) p2 :=
    r_seq_cell (fst p1) (fst p2) && r_cell (snd p1) (snd p2).

Lemma c_opening_cells_aux p1 p2 out1 out2 low1 low2 high1 high2 :
  a_pt p1 == p2 ->
  r_seq_edge out1 out2 ->
  r_edge low1 low2 ->
  r_edge high1 high2 ->
  all (fun g=> generic_trajectories.pt_eqb R eq_op (p_left_pt g)
               p1) out1 ->
  generic_trajectories.valid_edge R le plain_edge p_left_pt p_right_pt
    low1 p1 ->
  generic_trajectories.valid_edge R le plain_edge p_left_pt p_right_pt
    high1 p1 ->
  r_prod_seq_cell_cell
  (generic_trajectories.opening_cells_aux R eq_op le +%R (fun x y => x - y) *%R 
  (fun x y => x / y) 0 plain_edge plain_Bedge p_left_pt p_right_pt
  p1 out1 low1 high1)
  (opening_cells_aux p2 out2 low2 high2).
Proof.
move=> cnd_p cnd_out cnd_low cnd_high oute vle vhe.
elim: out1 out2 low1 low2 cnd_out cnd_low oute vle => [ | g1 gs Ih] [ | g2 gs2] //.
  move=> low1 low2 _ cnd_low _ vle /=.
  have svl := c_valid_edge cnd_low cnd_p.
  have vle2 : valid_edge low2 p2.
    by rewrite -svl.
  have := c_vertical_intersection_point cnd_p cnd_low.
  rewrite (pvertE vle2).
  case: generic_trajectories.vertical_intersection_point => [ pl | ] //.
  rewrite /r_option_pt => plq.
  have svh := c_valid_edge cnd_high cnd_p.
  have vhe2 : valid_edge high2 p2.
    by rewrite -svh.
  have := c_vertical_intersection_point cnd_p cnd_high.
  rewrite (pvertE vhe2).
  case: generic_trajectories.vertical_intersection_point => [ ph | ] //.
  rewrite /r_option_pt => phq.
  rewrite /r_prod_seq_cell_cell /= /r_cell /= cnd_low cnd_high !andbT.
  by apply: c_no_dup_seq; rewrite /= plq phq cnd_p.
move=> low1 low2 /= /andP[] cnd_g cnd_gs cnd_low /andP[] lg oute vl.
have vl2 : valid_edge low2 p2.
  by rewrite -(c_valid_edge cnd_low cnd_p).
have vg : generic_trajectories.valid_edge R le plain_edge p_left_pt
      p_right_pt g1 p1.
  rewrite /generic_trajectories.valid_edge.
  rewrite c_pt_eqb in lg.
  rewrite !(c_a_pt_x).
  rewrite (eqP lg) le_refl /= !(c_a_pt_x) -(eqP lg).
  have := cnd_g=> /andP[] /eqP -> /eqP ->.
  by case: (g2)=> /= a b /ltW.
have vg2 : valid_edge g2 p2.
  by rewrite -(c_valid_edge cnd_g cnd_p).
have := Ih gs2 g1 g2 cnd_gs cnd_g oute vg.
case: generic_trajectories.opening_cells_aux => [nos1 lno1].
case: opening_cells_aux=> [nos2 lno2]=> {Ih} /andP[]/= Ih1 Ih2.
have := c_vertical_intersection_point cnd_p cnd_low.
rewrite (pvertE vl2).
case: generic_trajectories.vertical_intersection_point => [p' | ] //=.
move=> cnd_p'.
rewrite /r_prod_seq_cell_cell /= {1}/r_cell /= cnd_low Ih1 Ih2 cnd_g !andbT.
by apply: c_no_dup_seq; rewrite /= cnd_p cnd_p'.
Qed.

Definition r_option_seq_cell_up_3 v1 v2 :=
  match v1, v2 with
  | None, None => true
  | Some (s1, s2, s3), Some (s4, s5, s6) =>
    r_seq_cell s1 s4 && r_seq_cell s2 s5 && r_seq_cell s3 s6
  | _, _ => false
  end.
