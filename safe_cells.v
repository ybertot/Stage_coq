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
Variables bottom top : edge.
Variable obstacles : seq edge.
Variables points : seq pt.

Hypothesis obstacles_sub :
  {subset [seq low c | c <- closed] ++
     [seq high c | c <- closed] <= bottom :: top :: obstacles}.

Hypothesis obstacles_point_in :
  {subset [seq left_pt g | g <- obstacles] ++
    [seq right_pt g | g <- obstacles] <= points}.

Hypothesis disj_closed :  {in closed &, disjoint_closed_cells R}.
(*
Hypothesis disj_open :  {in [:: o_cell] & closed, disjoint_open_closed_cells R}*)

Hypothesis coverage : {in obstacles, forall g, edge_covered g [::] closed}.
Hypothesis covered_points :
   {in points, forall p, exists2 c, c \in closed & p \in right_pts c /\
       (p >>> low c)}.

Hypothesis non_empty_closed : {in closed, forall c, exists p,
  [&& p >>> low c, p <<< high c & left_limit c < p_x p < right_limit c]}.
Hypothesis closed_ok : {in closed, forall c, closed_cell_side_limit_ok c}.
Hypothesis noc : {in bottom :: top :: obstacles &,
  forall g1 g2, inter_at_ext g1 g2}.
Hypothesis low_high : {in closed, forall c, low c <| high c}.
Hypothesis low_dif_high : {in closed, forall c, low c != high c}.

Lemma x_left_pts_left_limit (c : cell) (p : pt) :
  closed_cell_side_limit_ok c ->
  p \in left_pts c -> p_x p = left_limit c.
Proof.
move=> + pin; move=> /andP[] ln0 /andP[] lsx _.
by rewrite (eqP (allP lsx _ _)).
Qed.

Lemma x_right_pts_right_limit (c : cell) (p : pt) :
  closed_cell_side_limit_ok c ->
  p \in right_pts c -> p_x p = right_limit c.
Proof.
move=> + pin; move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
move=> /andP[] rn0 /andP[] rsx _.
by rewrite (eqP (allP rsx _ _)).
Qed.

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

Lemma right_valid :
  {in closed, forall c, {in right_pts c, forall p, 
      valid_edge (low c) p /\ valid_edge (high c) p}}.
Proof.
move=> c cin p pin.
have cok := closed_ok cin.
have [p' /andP[_ /andP[_ /andP[p'l p'r]]]] := non_empty_closed cin.
have lltr : left_limit c < right_limit c.
  by apply: (lt_trans p'l p'r).
split.
  apply/andP; split; rewrite (x_right_pts_right_limit cok pin).
    apply/(le_trans (left_limit_left_pt_low_cl cok)).
    by apply/ltW.
  by apply: right_limit_right_pt_low_cl.
apply/andP; split; rewrite (x_right_pts_right_limit cok pin).
  apply/(le_trans (left_limit_left_pt_high_cl cok)).
  by apply/ltW.
by apply: right_limit_right_pt_high_cl.
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

(* I don't know yet if this is going to be used. *)
Lemma above_low : {in closed, forall c p, p === high c -> p >>= low c}.
Proof.
move=> c cl p.
Admitted.


Lemma right_side_under_high (c : cell) p :
  closed_cell_side_limit_ok c ->
  valid_edge (high c) p ->
  p \in right_pts c ->
  p <<= high c.
Proof.
move=> cok vph pin.
set p' := {| p_x := p_x p; p_y := pvert_y p (high c)|}.
have sx: p_x p = p_x p' by rewrite /p'.
have p'on : p' === high c by apply: pvert_on vph.
rewrite (under_edge_lower_y sx) //.
have := cok.
do 5 move=> /andP[] _.
move=> /andP[] rn0 /andP[] rsx /andP[] srt /andP[] _ lon.
have p'q : p' = last (dummy_pt _) (right_pts c).
  have := on_edge_same_point p'on lon.
  rewrite (allP rsx _ pin)=> /(_ isT)=> samey.
  by apply/eqP; rewrite pt_eqE samey (allP rsx _ pin).
move: rn0 p'q pin srt.
elim/last_ind: (right_pts c) => [| rpts p2 Ih] // _ p'q pin srt.
move: pin; rewrite mem_rcons inE => /orP[/eqP -> | pin].
  by rewrite p'q last_rcons.
apply: ltW; rewrite p'q last_rcons.
move: srt; rewrite map_rcons=> srt.
by have := (allP (sorted_rconsE lt_trans srt)); apply; rewrite map_f.
Qed.

Lemma in_bound_closed_valid (c : cell) p :
  closed_cell_side_limit_ok c ->
  left_limit c <= p_x p -> p_x p <= right_limit c ->
  valid_edge (low c) p /\ valid_edge (high c) p.
Proof.
move=> cok lp pr.
have llh := left_limit_left_pt_high_cl cok.
have lll := left_limit_left_pt_low_cl cok.
have rrh := right_limit_right_pt_high_cl cok.
have rrl := right_limit_right_pt_low_cl cok.
split; rewrite /valid_edge.
  by rewrite (le_trans lll lp) (le_trans pr rrl).
by rewrite (le_trans llh lp) (le_trans pr rrh).
Qed.

Lemma left_side_under_high (c : cell) p :
  closed_cell_side_limit_ok c ->
  valid_edge (high c) p ->
  p \in left_pts c ->
  p <<= high c.
Proof.
move=> cok vph pin.
set p' := {| p_x := p_x p; p_y := pvert_y p (high c)|}.
have sx: p_x p = p_x p' by rewrite /p'.
have p'on : p' === high c by apply: pvert_on vph.
rewrite (under_edge_lower_y sx) //.
have := cok.
move=> /andP[] ln0 /andP[] lsx /andP[] srt /andP[] hon _.
have p'q : p' = head (dummy_pt _) (left_pts c).
  have := on_edge_same_point p'on hon.
  rewrite (eqP (allP lsx _ pin)).
  rewrite (x_left_pts_left_limit cok (head_in_not_nil _ ln0)) eqxx.
  move=> /(_ isT)=> samey.
  apply/eqP; rewrite pt_eqE samey andbT.
  rewrite (eqP (allP lsx _ pin)) eq_sym.
  by rewrite (allP lsx _ (head_in_not_nil _ ln0)).
move: ln0 p'q pin srt.
case: (left_pts c)=> [| p2 lpts] // _ p'q pin srt.
move: pin; rewrite inE => /orP[/eqP -> | pin].
  by rewrite p'q.
apply: ltW; rewrite p'q.
move: srt=> /=; rewrite (path_sortedE); last first.
  by move=> x y z xy yz; apply: (lt_trans yz xy).
by move=> /andP[] /allP/(_ (p_y p)) + _; apply; rewrite map_f.
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
rewrite le_eqVlt=> /orP[ /eqP pxq | ].
  have plg : p = left_pt g.
    move: lpcc; rewrite /= pxq=> /eqP samex.
    have := on_edge_same_point pong (left_on_edge _).
    rewrite samex=> /(_ isT) samey.
    by apply/eqP; rewrite pt_eqE samex samey.
  have pin : p \in points.
    apply: obstacles_point_in; rewrite mem_cat; apply/orP; left.
    by rewrite plg map_f.
  have [c' ccl' [pc'r p'al]] := (covered_points pin).
  have := disj_closed ccl ccl'.
  move=> [cqc' | ].
    have [p' /andP[] _ /andP[] _ /andP[] lp' p'r]:= non_empty_closed ccl'.
    move: pleft; rewrite cqc'.
    by rewrite (x_right_pts_right_limit (closed_ok ccl')) // lt_irreflexive.
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
  have [pr | pnr ] := eqVneq p (right_pt g).
    have [c' c'in [prc' pin']] : exists2 c', c' \in closed &
        p_x p = right_limit c' /\ inside_closed' p c'.
      have pp : p \in points.
        by apply/obstacles_point_in; rewrite pr mem_cat map_f // orbT.
      have [c' c'in [pr' pal']] := covered_points pp.
      exists c'; rewrite // inside_closed'E pal'.
      rewrite (x_right_pts_right_limit (closed_ok c'in)) // le_refl.
      have [q /andP[] _ /andP[] _ /andP[] Q1 Q2] := non_empty_closed c'in.
      rewrite (lt_trans Q1 Q2) ?andbT {q Q1 Q2}.
      have [vpl' vph'] := right_valid c'in pr'.
      by rewrite (right_side_under_high (closed_ok c'in)).
    have [cqc' | ] := disj_closed ccl c'in.
      by move: pleft; rewrite prc' cqc'; rewrite lt_irreflexive.
    by move=> /(_ p); rewrite pin' pinc.
  have noc1 : inter_at_ext (low pc1) (high pc1).
    by apply/noc; apply: obstacles_sub; rewrite mem_cat map_f //= ?orbT.
  have ponh : p === high pc1 by rewrite hpc1.
  have pin1 : inside_closed' p pc1.
    rewrite inside_closed'E under_onVstrict hpc1 // pong pc1lp /=.
    rewrite rpc1; move: vgp=> /andP[] _ ->; rewrite andbT.
    have := closed_cell_in_high_above_low (low_dif_high pc1cl) (low_high pc1cl)
    noc1 (closed_ok pc1cl) _ ponh; apply.
    rewrite pc1lp /= rpc1.
    move: (pong)=> /andP[] _ /andP[] _; rewrite le_eqVlt=> /orP[]; last by [].
    move=> abs.
    move: pnr=> /negP[]; rewrite pt_eqE abs /=.
    by have := on_edge_same_point pong (right_on_edge _) abs.
  have vph1 : valid_edge (high pc1) p by move: ponh=> /andP[].
  have [cqc' | ] := disj_closed ccl pc1cl.
    by move: puh; rewrite strict_nonAunder cqc' // ponh.
  by move=> /(_ p); rewrite pin1 pinc.
have pcccl' : {subset pc2 :: pcc <= closed}.
  by move=> c' c'in; apply: pcccl; rewrite inE c'in orbT.
have highs' : {in pc2 :: pcc, forall c, high c = g}.
  by move=> c' c'in; apply highs; rewrite inE c'in orbT.
have conn' : connect_limits (pc2 :: pcc).
  by move: conn; rewrite /= => /andP[].
have rpcc' : right_limit (last_cell (pc2 :: pcc)) = p_x (right_pt g).
  by exact: rpcc.
have [pleft2 | pright2 ] := lerP (p_x p) (left_limit pc2).
(* In this case, p is inside pc1, contradiction with pinc *)
  have v1 : valid_edge g p by move: pong=> /andP[].
  have pc1cl : pc1 \in closed by apply: pcccl; rewrite inE eqxx.  
  suff pin1 : inside_closed' p pc1.
    have [cqpc1 | ] := disj_closed ccl pc1cl.
      move: puh; rewrite cqpc1 (highs _ (mem_head _ _)) strict_nonAunder //.
      by rewrite pong.
  by move=> /(_ p); rewrite pin1 pinc.
  rewrite inside_closed'E.
  have r1l2 : right_limit pc1 = left_limit pc2.
    by apply/eqP; move: conn=> /= /andP[].
  move: (conn)=> /= /andP[] /eqP -> _; rewrite pleft2 pc1lp !andbT.
  rewrite (highs _ (mem_head _ _)) under_onVstrict // pong /=.
  have ponh : p === high pc1 by rewrite (highs _ (mem_head _ _)).
  have noc1 : inter_at_ext (low pc1) (high pc1).
    by apply/noc; apply: obstacles_sub; rewrite mem_cat map_f //= ?orbT.
  move: (pleft2); rewrite le_eqVlt=> /orP[/eqP pat | pltstrict]; last first.
    have := closed_cell_in_high_above_low (low_dif_high pc1cl) (low_high pc1cl)
      noc1 (closed_ok pc1cl) _ ponh; apply.
    move: (conn)=> /= /andP[] /eqP -> _.
    by rewrite pltstrict pc1lp.
  have sl : p_x (left_pt g) < p_x p.
    have llh := left_limit_left_pt_high_cl (closed_ok pc1cl).
    by rewrite -(highs _ (mem_head _ _)); apply: (le_lt_trans llh).
  have pc2cl : pc2 \in closed by apply: pcccl'; rewrite mem_head.
  have sr : p_x p < p_x (right_pt g).
    rewrite pat.
    have [p' /andP[] _ /andP[] _ /andP[] l2p' p'r2] := non_empty_closed pc2cl.
    rewrite (lt_trans l2p') // (lt_le_trans p'r2) //.
    have := right_limit_right_pt_high_cl (closed_ok pc2cl).
    by rewrite (highs' _ (mem_head _ _)).
  have [vl1 vh1] : valid_edge (low pc1) p /\ valid_edge (high pc1) p.
    have := in_bound_closed_valid (closed_ok pc1cl) (ltW pc1lp).
    by rewrite pat r1l2 le_refl=> /(_ isT).
  have := above_low pc1cl ponh.
  rewrite strict_nonAunder // negb_and negbK=> /orP[] ponl; last by [].
  have lo : low pc1 \in bottom :: top :: obstacles.
    by apply: obstacles_sub; rewrite mem_cat map_f.
  have ho : high pc1 \in bottom :: top :: obstacles.
    by apply: obstacles_sub; rewrite mem_cat map_f ?orbT.
  have [lqh | ] := noc ho lo.
    by have := low_dif_high pc1cl; rewrite lqh eqxx.
  move=> /(_ p ponh ponl); rewrite !inE=> /orP[]/eqP pext.
    by move: sl; rewrite pext (highs _ (mem_head _ _)) lt_irreflexive.
  by move: sr; rewrite pext (highs _ (mem_head _ _)) lt_irreflexive.
(* In this case, we use the induction hypothesis *)
by have := Ih pc2 pcccl' highs' conn' rpcc' pright2.
Qed.

End safety_property.


Section main_statement.

Variable R : realFieldType.

Lemma start_yields_safe_cells evs bottom top (open closed : seq (cell R)):
  sorted (fun e1 e2 => p_x (point e1) < p_x (point e2)) evs ->
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in [:: bottom, top & 
         events_to_edges evs] &, forall e1 e2, inter_at_ext e1 e2} ->
  {in events_to_edges evs,
         forall g : edge R,
         inside_box bottom top (left_pt g) &&
         inside_box bottom top (right_pt g)} ->
  all (inside_box bottom top) [seq point e | e <- evs] ->
  sorted (lexPtEv (R:=R)) evs ->
  {in evs, forall ev : event R, out_left_event ev} ->
  close_edges_from_events evs ->
  {in events_to_edges evs & evs, forall g e, non_inner g (point e)} ->
  {in evs, forall e, uniq (outgoing e)} ->
  start evs bottom top = (open, closed) ->
  {in closed & events_to_edges evs, forall c g p,
    strict_inside_closed p c -> ~~(p === g)}.
Proof.
move=> general_position bottom_below_top startok no_crossing.
move=> all_edges_in all_points_in sorted_lex out_edges_correct.
move=> edges_closed no_event_in_edge outgoing_event_unique start_eq.
have [closed_has_disjoint_cells no_intersection_closed_open]:=
   start_disjoint_general_position general_position bottom_below_top
   startok no_crossing all_edges_in all_points_in sorted_lex (@subset_id _ _)
   out_edges_correct edges_closed start_eq.
have [all_edges_covered all_points_covered]:=
   start_edge_covered_general_position general_position bottom_below_top
   startok no_crossing all_edges_in all_points_in sorted_lex (@subset_id _ _)
   out_edges_correct edges_closed no_event_in_edge outgoing_event_unique
   start_eq.
have [closed_main_properties [subcl all_closed_ok]] :=
   start_safe_sides general_position bottom_below_top startok no_crossing
   all_edges_in all_points_in sorted_lex (@subset_id _ _) out_edges_correct
   edges_closed no_event_in_edge outgoing_event_unique start_eq.
move=> c g cin gin p pin.
set ref_points := [seq point e | e <- evs].
(* TODO : decide on moving this to a separate lemma. *)
have sub_ref : {subset [seq left_pt g | g <- events_to_edges evs] ++
                  [seq right_pt g | g <- events_to_edges evs] <=
                  ref_points}.
  rewrite /ref_points.
  move: edges_closed out_edges_correct.
  elim: (evs) => [ | ev evs' Ih] //= => /andP [cl1 /Ih {}Ih].
  move=> out_evs.
  have oute : out_left_event ev by apply: out_evs; rewrite mem_head.
  have {}out_evs : {in evs', forall ev, out_left_event ev}.
   by move=> e ein; apply: out_evs; rewrite inE ein orbT.
  have {}Ih := Ih out_evs.
  rewrite events_to_edges_cons.
  move=> q; rewrite mem_cat=> /orP[] /mapP[e + ->].
    rewrite mem_cat => /orP[/oute/eqP -> | ein ]; first by rewrite mem_head.
    rewrite inE; apply/orP; right; apply: Ih.
    by rewrite mem_cat map_f.
  rewrite mem_cat=> /orP[/(allP cl1)/hasP[e' e'in /eqP ->] | e'in].
    by rewrite inE map_f ?orbT.
  rewrite inE; apply/orP; right; apply: Ih.
  by rewrite mem_cat map_f ?orbT.
have missing_fact1 :
  {in events_to_edges evs, forall g, cells.edge_covered g [::] closed}.
  admit.
have missing_fact2 :
 {in closed, forall c, exists p,
   [&& p >>> low c, p <<< high c & left_limit c < p_x p < right_limit c]}.
  admit.
have rf_cl : {in closed, forall c, low c <| high c}.
  by move=> c' c'in; have [it _] := closed_main_properties _ c'in.
have dif_lh_cl : {in closed, forall c, low c != high c}.
  by move=> c' c'in; have [_ [it _]] := closed_main_properties _ c'in.
have points_covered' : {in [seq left_pt g0 | g0 <- events_to_edges evs] ++
       [seq right_pt g0 | g0 <- events_to_edges evs],
     forall p0 : pt_eqType R,
     exists2 c0 : cell_eqType R,
       c0 \in closed & p0 \in right_pts c0 /\ p0 >>> low c0}.
  by move=> q /sub_ref/mapP[e ein ->]; apply: all_points_covered.
have puh : p <<< high c.
  by move: pin; rewrite /strict_inside_closed => /andP[] /andP[].
have pal : p >>> low c.
  by move: pin; rewrite /strict_inside_closed => /andP[] /andP[].
have p_between : left_limit c < p_x p < right_limit c.
  by move: pin; rewrite /strict_inside_closed=> /andP[].
by have := safe_cell_interior subcl (@subset_id _ _) closed_has_disjoint_cells
  missing_fact1 points_covered' missing_fact2 (allP all_closed_ok)
  no_crossing rf_cl dif_lh_cl cin puh pal p_between gin.
