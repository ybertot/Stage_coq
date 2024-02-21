From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import math_comp_complements points_and_edges events cells.
Require Import opening_cells cells_alg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section safety_property.

Variable R : realFieldType.

Notation cell := (@cell R).
Notation pt := (@pt R).
Notation edge := (@edge R).

Variables closed : seq cell.
(* The last open cell.  We need to prove that that its top edge is top.
   Then, coverage will be given for all obstacles by the fact that all
   edges in obstacles are different from top. *)
Variable o_cell : cell.
Variables bottom top : cell.
Variable obstacles : seq edge.
Variables points : seq pt.

Hypothesis obstacles_in :
  {subset [seq left_pt g | g <- obstacles] ++ [seq right_pt g | g <- obstacles]
     <= points}.

Hypothesis disj_closed :  {in closed &, disjoint_closed_cells R}.
Hypothesis disj_open :  {in [:: o_cell] & closed, disjoint_open_closed_cells R}.
Hypothesis coverage : {in obstacles, forall g, edge_covered g [::] closed}.
Hypothesis covered_points :
   {in points, forall p, exists2 c, c \in closed & p \in right_pts c /\
       (p >>> low c)}.

Hypothesis non_empty_closed : {in closed, forall c, exists p,
  [&& p >>> low c, p <<< high c & left_limit c < p_x p < right_limit c]}.
Hypothesis closed_ok : {in closed, forall c, closed_cell_side_limit_ok c}.
Hypothesis noc : {in obstacles &, forall g1 g2, inter_at_ext g1 g2}.

Lemma above_low : {in closed, forall c p, p === high c -> p >>= low c}.
Admitted.

Lemma left_limit_left_pt_high_cl (c : cell) :
  closed_cell_side_limit_ok c ->
  p_x (left_pt (high c)) <= left_limit c.
Proof.
move=> /andP[] ln0 /andP[] lsx /andP[] _ /andP[] /andP[] _ /andP[] + _ _.
by rewrite (eqP (allP lsx _ (head_in_not_nil _ ln0))).
Qed.

Lemma right_limit_right_pt_high_cl (c : cell) :
  closed_cell_side_limit_ok c ->
  right_limit c <= p_x (right_pt (high c)).
Proof.
move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
move=> /andP[] rn0 /andP[] rsx /andP[] _ /andP[] _ /andP[] _ /andP[] _. 
by rewrite (eqP (allP rsx _ (last_in_not_nil _ rn0))).
Qed.

Lemma left_limit_left_pt_low_cl (c : cell) :
  closed_cell_side_limit_ok c ->
  p_x (left_pt (low c)) <= left_limit c.
Proof.
move=> /andP[] ln0 /andP[] lsx /andP[] _ /andP[] _ /andP[].
move=> /andP[] _ /andP[] + _ _.
by rewrite (eqP (allP lsx _ (last_in_not_nil _ ln0))).
Qed.

Lemma right_limit_right_pt_low_cl (c : cell) :
  closed_cell_side_limit_ok c ->
  right_limit c <= p_x (right_pt (low c)).
Proof.
move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
move=> /andP[] rn0 /andP[] rsx /andP[] _ /andP[] /andP[] _ /andP[] _ + _.
by rewrite (eqP (allP rsx _ (head_in_not_nil _ rn0))).
Qed.

Lemma closed_cell_in_high_above_low p (c : cell) :
  low c != high c ->
  low c <| high c ->
  inter_at_ext (low c) (high c) ->
  closed_cell_side_limit_ok c ->
  left_limit c < p_x p < right_limit c ->
  p === high c -> p >>> low c.
Proof.
move=> dif bel noclh cok /andP[] midl midr on.
have [vlp vhp] : valid_edge (low c) p /\ valid_edge (high c) p.
  move: cok=> /andP[] ln0 /andP[] lsx /andP[].
  move=> _ /andP[] /andP[] _ /andP[] lh _ /andP[] /andP[] _ /andP[] ll _.
  move=> /andP[] rn0 /andP[] rsx /andP[].
  move=> _ /andP[] /andP[] _ /andP[] _ rl /andP[] _ /andP[] _ rh.
  rewrite (eqP (allP lsx _ (last_in_not_nil (dummy_pt _) ln0))) in ll.
  rewrite (eqP (allP rsx _ (head_in_not_nil (dummy_pt _) rn0))) in rl.
  rewrite (eqP (allP lsx _ (head_in_not_nil (dummy_pt _) ln0))) in lh.
  rewrite (eqP (allP rsx _ (last_in_not_nil (dummy_pt _) rn0))) in rh.
  split; rewrite /valid_edge.
    by rewrite (ltW (le_lt_trans ll midl)) (ltW (lt_le_trans midr rl)).
  by rewrite (ltW (le_lt_trans lh midl)) (ltW (lt_le_trans midr rh)).
rewrite under_onVstrict // negb_or.
move: noclh=> [abs | noclh]; first by rewrite abs eqxx in dif.
apply/andP; split; last first.
  apply/negP=> abs.
  have := order_edges_strict_viz_point' vlp vhp bel abs.
  by rewrite strict_nonAunder // on.
apply/negP=> abs.
have := noclh _ abs on; rewrite !inE=> /orP[] /eqP {}abs.
  move: midl; apply/negP; rewrite -leNgt abs.
  by apply: left_limit_left_pt_low_cl.
(* TODO: at this place, the typechecking loops, this warrants a bug report. *)
(*(  have := left_limit_max cok. *)
move: midr; apply/negP; rewrite -leNgt abs.
by apply: right_limit_right_pt_low_cl.
Qed.

Lemma safe_cell_interior c p :
  c \in closed -> p <<< high c -> p >>> low c ->
  left_limit c < p_x p < right_limit c ->
  {in obstacles, forall g, ~~ (p === g)}.
Proof.
move=> ccl puh pal /andP[] pright pleft g gin; apply/negP=> pong.
have pinc : inside_closed' p c.
  by rewrite inside_closed'E (underW puh) pal pright (ltW pleft).
have [[opc [pccs [pccssub [highs [cpccs [opco lopcq]]]]]] | ] := coverage gin.
  by [].
move=> [[ | pc1 pcc] [pccn0 [pcccl [ highs [conn [lpcc rpcc]]]]]].
  by [].
have : left_limit pc1 <= p_x p.
  by move:(pong)=> /andP[] _ /andP[]; rewrite lpcc.
rewrite le_eqVlt=> /orP[/eqP pxq | ].
  have plg : p = left_pt g by admit.
  have pin : p \in points.
    apply: obstacles_in; rewrite mem_cat; apply/orP; left.
    by rewrite plg map_f.
  have [c' ccl' [pc'r p'al]] := (covered_points pin).
  have := disj_closed ccl ccl'.
  move=> [].
    admit.
  move=> /(_ p); rewrite pinc=> /negP; apply.
  rewrite inside_closed'E p'al.
  have c'ok := closed_ok ccl'.
  have /andP[_ /andP[_ /andP[_ /andP[_ /andP[_ ]]] ]] := c'ok.
  move=> /andP[rn0 /andP[samex /andP[srt /andP[onlow onhigh]]]].
  have prlq : p_x p = right_limit c' by apply/eqP/(allP samex).
  rewrite (under_edge_lower_y prlq onhigh).
  have -> /= : p_y p <= p_y (last (dummy_pt R) (right_pts c')).
    elim/last_ind:{-1} (right_pts c') (erefl (right_pts c'))=>[| ps pn _] psq.
      by rewrite psq in rn0.
    move: pc'r; rewrite psq mem_rcons inE => /orP[/eqP -> | pps].
      by rewrite last_rcons.
    move: (srt); rewrite psq map_rcons => srt'.
    have := sorted_rconsE lt_trans srt'=> /allP/(_ _ (map_f _ pps))/ltW.
    by rewrite last_rcons.
  have [p1 /andP[_ /andP[ _ /andP[A B]]]] := non_empty_closed ccl'.
  by rewrite prlq (lt_trans A B) le_refl.
elim: pcc pc1 pcccl highs conn rpcc {lpcc pccn0} =>
  [ | pc2 pcc Ih] pc1 pcccl highs conn rpcc pc1lp.
  have pc1cl : pc1 \in closed by apply: pcccl; rewrite inE eqxx.  
  have hpc1 : high pc1 = g by apply: (highs _ (mem_head _ _)).
  move: rpcc; rewrite /last_cell/= => rpc1.
  have vgp : valid_edge g p by move: pong=> /andP[].
  have in1 : inside_closed' p pc1.
    rewrite inside_closed'E under_onVstrict hpc1 // pong pc1lp /=.
    rewrite rpc1; move: vgp=> /andP[] _ ->; rewrite andbT.

move: lpcc; rewrite le_eqVlt=> /orP[/eqP onleft | ].
  (* We probably need to show that every closed cell has a closed
     neighbor on the left, except for the first one, but in this case
     p cannot be inside the closed cell c,
     So there is another cell, in which p is inside_closed', and disjointness
     should make it possible to conclude. *)
  admit.
elim : pcc pc1 pcccl highs conn rpcc {pccn0} => [ | pc2 pcc Ih]
  pc1 pcccl highs conn rpcc lpcc.
  (* if pc1 == c, there is a contradiction, because p <<< high c but
     p === high pc1 *)
  (* if pc1 != c we need to perform another case analysis.
        pf p === low pc1, then we p must be an event, and there exist
        another cell c' such that inside_closed' p  c' and p_x p = left_limit c'
        and c' != c, because  left_limit c <   beurk. *)
