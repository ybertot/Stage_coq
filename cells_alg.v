From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import math_comp_complements points_and_edges events cells.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section working_environment.

Variable R : realFieldType.

Notation pt := (pt R).
Notation edge := (edge R).
Notation event := (event R).

Notation cell := (cell R).

Notation dummy_pt := (dummy_pt R).
Notation dummy_edge := (dummy_edge R).
Notation dummy_cell := (dummy_cell R).

(* this function removes consecutives duplicates, meaning the seq needs
 to be sorted first if we want to remove all duplicates *)
Fixpoint no_dup_seq (A : eqType) (s : seq A) : (seq A) :=
  match s with
  | [::] => [::]
  | a::q => match q with
            | [::] => s
            | b::r => if a == b then no_dup_seq q else a::(no_dup_seq q)
            end
    end.

Definition close_cell (p : pt) (c : cell) :=
  match vertical_intersection_point p (low c),
        vertical_intersection_point p (high c) with
  | None, _ | _, None => c
  | Some p1, Some p2 => 
    Bcell (left_pts c) (no_dup_seq [:: p1; p; p2]) (low c) (high c)
  end.

Definition closing_cells (p : pt) (contact_cells: seq cell) : seq cell :=
  [seq close_cell p c | c <- contact_cells].

Lemma close_cell_preserve_3sides p c :
  [/\ low (close_cell p c) = low c,
      high (close_cell p c) = high c &
      left_pts (close_cell p c) = left_pts c].
Proof.
rewrite /close_cell.
case: (vertical_intersection_point p (low c))=> [p1 | ] //.
by case: (vertical_intersection_point p (high c))=> [p2 | ].
Qed.

Fixpoint opening_cells_aux (p : pt) (out : seq edge) (low_e high_e : edge) 
  : seq cell * cell :=
      match out with
    | [::] => let op0 := vertical_intersection_point p low_e in
              let op1 := vertical_intersection_point p high_e in
                      match (op0,op1) with
                          |(None,_) |(_,None)=> ([::], dummy_cell)
                          |(Some(p0),Some(p1)) =>
                              ([::] , Bcell  (no_dup_seq ([:: p1; p; p0])) [::] low_e high_e)                      end
    | c::q => let op0 := vertical_intersection_point p low_e in
              let (s, nc) := opening_cells_aux p q c high_e in
                    match op0 with
                       | None => ([::], dummy_cell)
                       | Some(p0) =>
                        (Bcell  (no_dup_seq([:: p; p0])) [::] low_e c :: s,
                         nc)
                    end
end.

Definition opening_cells (p : pt) (out : seq edge) (l h : edge) : seq cell :=
   let (s, c) := opening_cells_aux p (sort (@edge_below R) out) l h in
   rcons s c.

Fixpoint open_cells_decomposition_contact open_cells pt :
   option (seq cell * seq cell * cell) :=
if open_cells is c :: q then
  if contains_point pt c then
    if open_cells_decomposition_contact q pt is Some(cc, lc, c') then
       Some(c :: cc, lc, c')
     else
       Some([::], q, c)
  else
    None
else
  None.

Fixpoint open_cells_decomposition_rec open_cells pt : 
  seq cell * seq cell * cell * seq cell :=
if open_cells is c :: q then
  if contains_point pt c then
     if open_cells_decomposition_contact q pt is Some(cc, lc, c') then
        ([::], c :: cc, c', lc)
     else
        ([::], [::], c, q)
  else
    let '(fc, cc, c', lc) := open_cells_decomposition_rec q pt in
    (c :: fc, cc, c', lc)
else
  ([::], [::], dummy_cell, [::]).

Definition open_cells_decomposition (open_cells : seq cell) (p : pt) :
   seq cell * seq cell * cell * seq cell * edge * edge :=
let '(fc, cc, c', lc) := open_cells_decomposition_rec open_cells p in
(fc, cc, c', lc, low (head c' cc), high c').

Record scan_state :=
  Bscan {sc_open1 : seq cell;
         lst_open : cell;
         sc_open2 : seq cell;
         sc_closed : seq cell;
         lst_closed : cell;
         lst_high : edge;
         lst_x : R}.

Definition update_closed_cell (c : cell) (p : pt) : cell :=
  let ptseq := right_pts c in
  let newptseq :=
    (belast  (head (cells.dummy_pt R) ptseq) (behead ptseq)) ++
    [:: p; last (cells.dummy_pt R) ptseq] in
  Bcell (left_pts c) newptseq (low c) (high c).

Definition update_open_cell (c : cell) (e : event) : seq cell * cell :=
  if outgoing e is nil then
     let ptseq := left_pts c in
     let newptseq :=
       [:: head (cells.dummy_pt R) ptseq, point e & behead ptseq] in
     ([::], Bcell newptseq (right_pts c) (low c) (high c))
  else
    opening_cells_aux (point e) (sort (@edge_below _) (outgoing e))
        (low c) (high c).

Definition update_open_cell_top (c : cell) (new_high : edge) (e : event) :=
  if outgoing e is nil then
    let newptseq :=
      [:: Bpt (p_x (point e)) (pvert_y (point e) new_high) &
          left_pts c] in
      ([::], Bcell newptseq (right_pts c) (low c) new_high)
  else
    opening_cells_aux (point e) (sort (@edge_below _) (outgoing e))
        (low c) new_high.

Definition step (e : event) (st : scan_state) : scan_state :=
   let p := point e in
   let '(Bscan op1 lsto op2 cls cl lhigh lx) := st in
   if (p_x p != lx) then
     let '(first_cells, contact_cells, last_contact, last_cells, 
           lower_edge, higher_edge) :=
       open_cells_decomposition (op1 ++ lsto :: op2) p in
     let closed := closing_cells p contact_cells in
     let last_closed := close_cell p last_contact in
     let closed_cells := cls++closed in
     let (new_open_cells, newlastopen) :=
       opening_cells_aux p (sort (@edge_below _) (outgoing e))
            lower_edge higher_edge in
     Bscan (first_cells ++ new_open_cells)
           newlastopen last_cells closed_cells 
           last_closed  higher_edge (p_x (point e))
   else if p >>> lhigh then
     let '(fc', contact_cells, last_contact, last_cells,
           low_edge, higher_edge) :=
       open_cells_decomposition op2 p in
     let first_cells := op1 ++ lsto :: fc' in
(* TODO code duplication (6 lines above) *)
     let closed := closing_cells p contact_cells in
     let last_closed := close_cell p last_contact in
     let closed_cells := cls++closed in
     let (new_open_cells, newlastopen) :=
       opening_cells_aux p (sort (@edge_below _) (outgoing e))
            low_edge higher_edge in
     Bscan (first_cells ++ new_open_cells)
           newlastopen last_cells closed_cells last_closed
            higher_edge (p_x (point e))
   else if p <<< lhigh then 
     let new_closed := update_closed_cell cl (point e) in
     let (new_opens, new_lopen) := update_open_cell lsto e in
     Bscan (op1 ++ new_opens) new_lopen op2 cls new_closed lhigh lx
   else (* here p === lhigh *)
     let '(fc', contact_cells, last_contact, last_cells, lower_edge,
                higher_edge) :=
       open_cells_decomposition (lsto :: op2) p in
     let closed := closing_cells p contact_cells in
     let last_closed := close_cell p last_contact in
     let (new_opens, new_lopen) := update_open_cell_top lsto higher_edge e in
     Bscan (op1 ++ fc' ++ new_opens) new_lopen last_cells
          (cls ++ closed) last_closed higher_edge lx.

Definition leftmost_points (bottom top : edge) :=
  if p_x (left_pt bottom) < p_x (left_pt top) then
    if vertical_intersection_point (left_pt top) bottom is Some pt then
       [:: left_pt top; pt]
    else
        [::]
  else
     if vertical_intersection_point (left_pt bottom) top is Some pt then
        [:: pt; left_pt bottom]
     else
        [::].

Definition rightmost_points (bottom top : edge) :=
  if p_x (right_pt bottom) < p_x (right_pt top) then
    if vertical_intersection_point (right_pt bottom) top is Some pt then
       [:: right_pt bottom; pt]
    else
        [::]
  else
     if vertical_intersection_point (left_pt top) bottom is Some pt then
        [:: pt; right_pt top]
     else
        [::].

Definition complete_last_open (bottom top : edge) (c : cell) :=
  match c with
  | Bcell lpts rpts le he =>
      Bcell lpts (rightmost_points bottom top) le he
  end.

Fixpoint scan (events : seq event) (st : scan_state)
  : seq cell * seq cell :=
  match events, st with
     | [::], Bscan op1 lop op2 cl lcl _ _ =>
       (op1 ++ lop :: op2, lcl :: cl)
     | e::q, _ => scan q (step e st)
  end.

Definition start_open_cell (bottom top : edge) :=
  Bcell (leftmost_points bottom top) [::] bottom top.

Definition start (events : seq event) (bottom : edge) (top : edge) :
  seq cell * seq cell :=
  match events with
  | nil => ([:: start_open_cell bottom top], nil)
  | ev0 :: events =>
    let (newcells, lastopen) :=
      opening_cells_aux (point ev0) (sort (@edge_below _) (outgoing ev0))
            bottom top in
      scan events (Bscan newcells lastopen nil nil
         (close_cell (point ev0) (start_open_cell bottom top))
         top (p_x (point ev0)))
  end.

Section proof_environment.
Variables bottom top : edge.

Notation extra_bot := (extra_bot bottom).
Notation end_edge := (end_edge bottom top).
Notation close_out_from_event := (close_out_from_event bottom top).
Notation close_edges_from_events :=
  (close_edges_from_events bottom top).
Notation close_alive_edges := (close_alive_edges bottom top).
Notation cells_bottom_top := (cells_bottom_top bottom top).
Notation inside_box := (inside_box bottom top).
Notation open_cell_side_limit_ok := (@open_cell_side_limit_ok R).
Notation seq_low_high_shift := (@seq_low_high_shift R).
Notation cover_left_of := (@cover_left_of _ bottom top).

Section open_cells_decomposition.

Lemma open_cells_decomposition_contact_none open_cells p :
  open_cells_decomposition_contact open_cells p = None ->
  open_cells != [::] -> ~~contains_point p (head dummy_cell open_cells).
Proof.
case : open_cells => [// | /= c0 q].
by case : ifP=> ? //;
  case: (open_cells_decomposition_contact _ _)=> // [] [] [] //.
Qed.

Lemma open_cells_decomposition_contact_main_properties open_cells p cc c' lc:
  open_cells_decomposition_contact open_cells p = Some (cc, lc, c') ->
  cc ++ c' :: lc = open_cells /\
  contains_point p c' /\
  {in cc, forall c, contains_point p c} /\
  (lc != [::] -> ~~ contains_point p (head c' lc)).
Proof.
elim: open_cells cc c' lc => [ // | c q Ih] cc c' lc.
rewrite /=; case: ifP => [ctpcc | nctpcc] //.
case occ_eq : (open_cells_decomposition_contact _ _)
       (@open_cells_decomposition_contact_none q p)
    => [[[cc1 lc1] c1] | ] nonecase [] <- <- <-; last first.
  split;[ by [] | split; [by [] | split; [by [] | ] ]].  
  by case: (q) nonecase => [// | c2 q2] ; apply.
have [eqls [ctc1 [allct nctlc1]]] := Ih _ _  _ occ_eq.
split; first by rewrite /=; congr (_ :: _).
split; first by [].
split; last by [].
by move=> w; rewrite inE => /orP[/eqP -> // | ]; apply: allct.
Qed.

Lemma open_cells_decomposition_main_properties open_cells p fc cc lcc lc le he:
  open_cells_decomposition open_cells p = (fc, cc, lcc, lc, le, he) ->
  (exists2 w, w \in open_cells & contains_point' p w) ->
  open_cells = fc ++ cc ++ lcc :: lc /\
  contains_point p lcc /\
  {in cc, forall c, contains_point p c} /\
  {in fc, forall c, ~~contains_point p c} /\
  (lc != [::] -> ~~ contains_point p (head lcc lc)) /\
  he = high lcc /\
  le = low (head lcc cc) /\
  le \in cell_edges open_cells /\
  he \in cell_edges open_cells.
Proof.
rewrite /open_cells_decomposition.
elim : open_cells fc cc lcc lc le he => [ | c q Ih] fc cc lcc lc le he.  
  by rewrite /= => _ [] w.
rewrite /=; case: ifP=> ctc.
  case ocdc_eq : (open_cells_decomposition_contact q p) => [ [[cc0 lc0] c0] | ].
    move=> [] <- <- <- <- <- <- _.
    have [qeq [ctc0 [allct nct]] ]:=
     open_cells_decomposition_contact_main_properties ocdc_eq.
    split; first by rewrite /= qeq.
    split; first by [].
    split; first by move=> c1 /orP[/eqP -> | ] //; apply: allct.
    split; first by [].
    split; first by [].
    split; first by [].
    split; first by [].
    by rewrite -qeq !mem_cat !map_f ?orbT // !(mem_cat, inE) eqxx ?orbT.
  move=> [] <- <- <- <- <- <- _.
  split; first by [].
  split; first by [].
  split; first by [].
  split; first by [].
  split.
    by move: (open_cells_decomposition_contact_none ocdc_eq); case: (q).
  split; first by [].
  split; first by [].
  by rewrite !mem_cat !map_f ?orbT // inE eqxx.
case ocdr_eq : (open_cells_decomposition_rec q p) => [[[fc1 cc1] lcc1] lc1].
move=> [] <- <- <- <- <- <- [] w win ctw.
have ex2 :exists2 w, w \in q & contains_point' p w.
  exists w; last by [].
  move: win ctw; rewrite inE => /orP[/eqP -> | //].
  by move=> /contains_point'W; rewrite ctc.
have := Ih fc1 cc1 lcc1 lc1 (low (head lcc1 cc1)) (high lcc1).
rewrite ocdr_eq => /(_ erefl ex2).
move=> [qeq [ctplcc1 [allct [allnct [nctlc [leeq heq]]]]]].
split; first by rewrite /= qeq.
split; first by [].
split; first by [].
split.
  by move=> c0; rewrite inE=> /orP[/eqP -> // | c0in]; rewrite ?ctc ?allnct.
split; first by [].
split; first by [].
split; first by [].
by rewrite qeq !mem_cat !map_f ?orbT //; case: (cc1) => [ | a b] /=;
 rewrite !(mem_cat, inE) eqxx ?orbT.
Qed.

Lemma decomposition_preserve_cells open_cells pt 
  first_cells contact last_contact last_cells low high_f:
(exists2 w, w \in open_cells & contains_point' pt w) ->
open_cells_decomposition open_cells pt  =
  (first_cells, contact, last_contact, last_cells, low, high_f) ->
open_cells = first_cells ++ contact ++ last_contact :: last_cells .
Proof.
move=> exc oe.
by have[] := open_cells_decomposition_main_properties oe exc.
Qed.

Lemma decomposition_connect_properties open_cells p 
  first_cells contact last_contact last_cells low_f high_f:
s_right_form open_cells ->
seq_valid open_cells p ->
adjacent_cells open_cells ->
cells_bottom_top open_cells ->
between_edges bottom top p ->
open_cells_decomposition open_cells p  =
  (first_cells, contact, last_contact, last_cells, low_f, high_f) ->
[/\ p >>> low_f, p <<< high_f, valid_edge low_f p, valid_edge high_f p &
forall c, (c \in first_cells) || (c \in last_cells) -> ~ contains_point p c].
Proof.
move=> rfo sval adj cbtom inbox_p oe.
have [w win ctw'] := exists_cell cbtom adj inbox_p.
have [ocd [ctpl [allct [allnct [nctlc [-> [-> _]]]]]]]:=
   open_cells_decomposition_main_properties oe (exists_cell cbtom adj inbox_p).
have [A B C D E] := 
  connect_properties cbtom adj rfo sval inbox_p ocd allnct allct ctpl nctlc.
by split => // c cin; apply/negP/E.
Qed.

Lemma decomposition_not_contain open_cells p : 
forall first_cells contact last_contact last_cells low_f high_f,
s_right_form open_cells ->
seq_valid open_cells p ->
adjacent_cells open_cells ->
cells_bottom_top open_cells ->
between_edges bottom top p ->
open_cells_decomposition open_cells p  =
  (first_cells, contact, last_contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) -> ~ contains_point p c.
Proof.
move => fc cc lcc lc low_f high_f rfo sval adj cbtom inbox_p oe c cin.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq leq]]]]]] :=
   open_cells_decomposition_main_properties oe 
          (exists_cell cbtom adj inbox_p).
by apply/negP; apply: (fclc_not_contain cbtom _ _ _ _ ocd).
Qed.

Lemma decomposition_not_end open_cells e :
forall first_cells contact last_contact last_cells low_f high_f,
s_right_form open_cells ->
seq_valid open_cells (point e) ->
adjacent_cells open_cells ->
cells_bottom_top open_cells ->
between_edges bottom top (point e) ->
open_cells_decomposition open_cells (point e) =
 (first_cells, contact, last_contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) ->
 ( ~ event_close_edge (low c) e) /\ ( ~ event_close_edge (high c) e).
Proof.
move=> fc cc lcc lc low_f high_f rfo sval adj cbtom inbox_p oe c cold.
have exi := exists_cell cbtom adj inbox_p.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq leq]]]]]]:=
   open_cells_decomposition_main_properties oe exi.
by apply: (fclc_not_end_aux cbtom adj _ sval inbox_p ocd _ lcc_ctn flcnct).
Qed.

Lemma l_h_in_open (open : seq cell) p :
cells_bottom_top open -> adjacent_cells open  ->
between_edges bottom top p ->
exists lc hc, lc \in open /\ hc \in open /\ low lc =
   snd(fst (open_cells_decomposition open p)) /\
   high hc = snd (open_cells_decomposition open p).
Proof.
move=> cbtom adj inbox_p.
case oe : (open_cells_decomposition open p) => [[[[[fc cc] lcc] lc] le] he].
have [ocd [_ [_ [_ [_ [heq [leq [lein hein]]]]]]]]:=
  open_cells_decomposition_main_properties oe
             (exists_cell cbtom adj inbox_p).
exists (head lcc cc), lcc.
split.
  by rewrite ocd !mem_cat; case: (cc) => [ | ? ?]; rewrite !inE eqxx !orbT.
split; first by rewrite ocd !(mem_cat, inE) eqxx !orbT.
by [].
Qed.

Lemma l_h_valid (open : seq cell) p :
cells_bottom_top open -> adjacent_cells open  ->
between_edges bottom top p ->
seq_valid open p ->
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition open p  = (first_cells, contact, last_cells, low_f, high_f) ->
valid_edge low_f p /\ valid_edge high_f p.
Proof.
rewrite /seq_valid.
move => cbtop adjopen insbox /allP openvalid.
have := (l_h_in_open cbtop adjopen insbox) => [] [lc [hc] ] /=.
move => [] /openvalid /andP [] validlowc _.
move => [] /openvalid /andP [] _ validhighc .
case op_c_d : (open_cells_decomposition open p) => [[[[fc cc]last_c ]low_e]high_e] /= => [][] <- <- .
by move => f_c contact last lowe highe [] _ _ _ <- <-.
Qed.

Lemma open_cells_decomposition_low_under_high open p fc cc lcc lc le he:
  {in [seq low c | c <- open] ++ [seq high c | c <- open] &, no_crossing R} ->
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  seq_valid open p ->
  s_right_form open ->
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  le <| he.
Proof.
move=> n_c cbtom adj inbox_p sval rfo oe.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [vle vhe]]]]]]]] :=
  open_cells_decomposition_main_properties oe
             (exists_cell cbtom adj inbox_p).
have := low_under_high cbtom adj rfo sval inbox_p ocd allnct allct lcc_ctn
  flcnct n_c.
by rewrite leq heq.
Qed.

Lemma open_cells_decomposition_contains open p fc cc lcc lc le he c:
  (exists2 c, c \in open & contains_point' p c) ->
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  c \in cc -> contains_point p c.
Proof.
move=> exi oe.
by have [_ [_ [/(_ c) + _]]] :=
   open_cells_decomposition_main_properties oe exi.
Qed.

Lemma open_cells_decomposition_point_on open p fc cc lcc lc le he c:
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  seq_valid open p ->
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  c \in cc -> p === high c.
Proof.

move=> cbtom adj inbox_p sval oe ccc.
have [ocd [lcc_ctn [allctn _]]]:= open_cells_decomposition_main_properties oe
           (exists_cell cbtom adj inbox_p).
by have := in_cc_on_high adj sval ocd allctn lcc_ctn ccc.
Qed.

Lemma last_first_cells_high open p fc cc lcc lc le he :
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  last bottom [seq high i | i <- fc] = le.
Proof.
move=> cbtom adj inbox_p oe.
have exi := exists_cell cbtom adj inbox_p.
have [ocd [_ [_ [_ [_ [heq [leq _]]]]]]] :=
   open_cells_decomposition_main_properties oe exi.
suff -> : last bottom [seq high i | i <- fc] = low (head lcc cc).
  by rewrite leq.
move: cbtom=> /andP[] /andP[] _ /eqP + _.
move : adj; rewrite ocd.
  elim/last_ind : {-1}(fc) (erefl fc) => [//= | fc' c1 _].
    by case: (cc) => [ | c2 cc'].
rewrite -cats1 -catA=> fceq /adjacent_catW /= [] _ + _.
rewrite cats1 map_rcons last_rcons.
by case: (cc) => [ | c2 cc'] /andP[] + _; rewrite /adj_rel /= => /eqP.
Qed.

Lemma high_in_first_cells_below open p first_cells cc lcc last_cells le he :
  open_cells_decomposition open p =
  (first_cells, cc, lcc, last_cells, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  seq_valid open p ->
  s_right_form open ->
  {in cell_edges open &, no_crossing R} ->
  {in [seq high i | i <- first_cells], forall g, p_x p < p_x (right_pt g)} ->
  {in [seq high c | c <- first_cells], forall g, g <| le}.
Proof.
move=> oe cbtom adj inbox_e sval rfo noc side_cond.
have exi := exists_cell cbtom adj inbox_e.
have [ocd _] := open_cells_decomposition_main_properties oe exi.
have vfc : {in [seq high i | i <- first_cells], forall g, valid_edge g p}.
  move=> g /mapP[c cin geq]; apply: (seq_valid_high sval).
  by apply/mapP; exists c=> //; rewrite ocd !mem_cat cin.
move=> g /mapP[c cin geq].
have [fc1 [fc2 fceq]] := mem_seq_split cin.
have cin' : c \in open by rewrite ocd !(mem_cat, inE) cin.
have := seq_edge_below' adj rfo; rewrite ocd fceq -[c :: _]/([:: c] ++ _).
set w := head _ _; rewrite -!catA (catA fc1) map_cat cat_path=> /andP[] _.
have tr : {in [seq high i | i <- first_cells] & &, transitive (@edge_below R)}.
  apply: (edge_below_trans _ vfc); first by left; exact side_cond.
  move: noc; apply: sub_in2=> g'; rewrite ocd cell_edges_cat 2!mem_cat => ->.
  by rewrite orbT.
rewrite cats1 map_rcons last_rcons map_cat cat_path=> /andP[] + _.
rewrite (path_sorted_inE tr); last first.
  apply/allP=> g' g'cnd; rewrite -[is_true _]/(is_true (g' \in (map _ _))) fceq.
  move: g'cnd; rewrite inE => /orP[/eqP -> | /mapP [g'c g'in ->]]; rewrite map_f // .
    by rewrite !(mem_cat, inE) eqxx orbT.
  by rewrite !(mem_cat, inE) g'in ?orbT.
have lastfirst := last_first_cells_high cbtom adj inbox_e oe.
move=>/andP[] /allP /(_ le); rewrite -lastfirst.
rewrite fceq !map_cat !last_cat /=.
case : (fc2) => [ | c' s'] //=; first by rewrite geq edge_below_refl.
by rewrite mem_last => /(_ isT); rewrite geq.
Qed.

Lemma head_last_cells_low open p fc cc lcc lc le he :
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  head top [seq low i | i <- lc] = he.
Proof.
move=> cbtom adj inbox_p oe.
have exi := exists_cell cbtom adj inbox_p.
have [ocd [_ [_ [_ [_ [-> _]]]]]] :=
   open_cells_decomposition_main_properties oe exi.
move: cbtom=> /andP[] _ /eqP.
move: adj; rewrite ocd => /adjacent_catW [] _ /adjacent_catW [] _ /=.
  rewrite !last_cat /=.
case : (lc) => [ | c2 lc'] //=.
by move=> /andP[] /eqP ->.
Qed.

(* Temporary trial, but this lemma might be better placed in
  points_and_edges. *)
Lemma decomposition_above_high_fc p open fc cc lcc lc le he c1:
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  s_right_form open ->
  seq_valid open p ->
  c1 \in fc -> p >>> high c1.
Proof.
move=> oe cbtom adj inbox_e rfo sval c1in.
have exi := exists_cell cbtom adj inbox_e.
have [ocd [_ [_ [_ [_ [heq leq]]]]]] :=
   open_cells_decomposition_main_properties oe exi.
have [pal puh vl vp _]:=
  decomposition_connect_properties rfo sval adj cbtom inbox_e oe.
rewrite under_pvert_y; last first.
  apply: (seq_valid_high sval).
  by apply/mapP; exists c1; rewrite // ocd !mem_cat c1in.
rewrite -ltNge.
have : pvert_y p le < p_y p.
  by move: pal; rewrite under_pvert_y // -ltNge.
apply: le_lt_trans.
move: c1in.
have [fceq | [fc' [lfc fceq]]] : fc = nil \/ exists fc' lfc, fc = rcons fc' lfc.
    by elim/last_ind : (fc) => [ | fc' lfc _];[left | right; exists fc', lfc].
  by rewrite fceq.
have := last_first_cells_high cbtom adj inbox_e oe.
rewrite fceq map_rcons last_rcons => <-.
rewrite mem_rcons inE => /orP[/eqP c1lfc | c1o]; first  by rewrite c1lfc.
have [a [b pab]] := mem_seq_split c1o.
move: fceq; rewrite pab -cats1 -catA /= => fceq.
(* requirement for path_edge_below_pvert_y *)
have req1 : all (valid_edge (R := _) ^~ p)
    [seq high i | i <- c1 :: b ++ [:: lfc]].
  apply/allP; apply: (sub_in1 _ (seq_valid_high sval)); apply: sub_map.
  by rewrite ocd fceq=> x; rewrite 2!mem_cat=> ->; rewrite orbT.
have req2 : path (@edge_below R) (high c1) [seq high i | i <- b ++ [:: lfc]].
  have := seq_edge_below' adj rfo.
  rewrite ocd (_ : fc = rcons a c1 ++ rcons b lfc); last first.
     by move: fceq; rewrite -!cats1 !catA /= -!catA /=.
  rewrite -!catA [X in path _ _ X]map_cat cat_path=> /andP[] _.
  rewrite !map_rcons last_rcons map_cat cat_path => /andP[] + _.
  by rewrite -cats1.
have : path (<=%R) (pvert_y p (high c1))
  [seq pvert_y p (high i) | i <- b ++ [:: lfc]].
  by have := path_edge_below_pvert_y req1 req2; rewrite -map_comp.
rewrite le_path_sortedE => /andP[] /allP + _.
move=> /(_ (pvert_y p (high lfc))); apply.
by apply/mapP; exists lfc => //=; rewrite mem_cat inE eqxx orbT.
Qed.

Lemma decomposition_under_low_lc p open fc cc lcc lc le he c1:
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  s_right_form open ->
  seq_valid open p ->
  c1 \in lc -> p <<< low c1.
Proof.
move=> oe cbtom adj inbox_e rfo sval c1in.
have exi := exists_cell cbtom adj inbox_e.
have [ocd _] := open_cells_decomposition_main_properties oe exi.
rewrite strict_under_pvert_y; last first.
    by apply/(seq_valid_low sval)/map_f; rewrite ocd !(mem_cat, inE) c1in ?orbT.
have [pal puh vl vp _]:=
  decomposition_connect_properties rfo sval adj cbtom inbox_e oe.
have puhe : p_y p < pvert_y p he.
  by move: puh; rewrite strict_under_pvert_y.
apply: (lt_le_trans puhe).
move: c1in; case lceq : lc => [ // | flc lc'] c1in.
have := head_last_cells_low cbtom adj inbox_e oe.
rewrite lceq /= => <-.
move: c1in; rewrite inE => /orP[/eqP c1flc | c1o]; first by rewrite c1flc.
have [a [b Pab]] := mem_seq_split c1o.
(* requirement for path_edge_below_pvert_y *)
have req1 : all (@valid_edge R ^~ p)
  [seq low i | i <- flc :: a ++ c1 :: b].
  apply/allP; apply: (sub_in1 _ (seq_valid_low sval)); apply: sub_map.
  by rewrite ocd lceq Pab=> x xin; rewrite 2!mem_cat inE xin ?orbT.
have req2 : path (@edge_below R) (low flc) [seq low i | i <- a ++ c1 :: b].
  have := seq_edge_below' adj rfo.
  have [on0 headq] : open != [::] /\ low (head dummy_cell open) = bottom.
    by move: cbtom=> /andP[] /andP[] + /eqP + _.
  have headq' : head dummy_edge [seq low i | i <- open] = bottom.
      by move: on0 headq; case: (open)=> [ // | ? ?] /=.
  rewrite headq' => pathoh.
  have : path (@edge_below R) bottom (bottom :: [seq high i | i <- open]).
      by rewrite /= edge_below_refl.
  have  := seq_low_high_shift on0 adj; rewrite headq => <-.
  rewrite -cats1 cat_path => /andP[] + _.
  rewrite ocd lceq Pab.
  by rewrite 2!map_cat 2!cat_path /= => /andP[] _ /andP[] _ /andP[] _ /andP[].
have : path (<=%R) (pvert_y p (low flc))
  [seq pvert_y p (low i) | i <- a ++ c1 :: b].
  by have := path_edge_below_pvert_y req1 req2; rewrite -map_comp.
rewrite le_path_sortedE => /andP[] /allP + _.
move=> /(_ (pvert_y p (low c1))); apply.
by apply/mapP; exists c1 => //=; rewrite !(mem_cat, inE, eqxx, orbT).
Qed.

End open_cells_decomposition.

Section opening_cells.

Lemma opening_cells_left p out le he :
  {in out, forall g, left_pt g == p} ->
  valid_edge le p ->
  valid_edge he p ->
  {in opening_cells p out le he, forall c, left_limit c = p_x p}.
Proof.
move=> outl vle vhe; rewrite /opening_cells.
have : forall g, g \in sort (@edge_below _) out -> left_pt g == p.
  by move=> g; rewrite mem_sort; apply outl.
elim: (sort _ _) le vle => [ | g1 gs Ih] le vle {}outl c.
  rewrite /= pvertE // pvertE //=.
  by case: ifP=> _; case: ifP=> _; rewrite inE /left_limit => /eqP ->.
have outl' : forall g, g \in gs -> left_pt g == p.
  by move=> g gin; apply outl; rewrite inE gin orbT.
rewrite /=.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (outl g1 _)) ?valid_edge_left // inE eqxx.
move: Ih; case oca_eq : (opening_cells_aux _ _ _ _) => [s c'] /(_ _ vg1 outl').
rewrite oca_eq => Ih.
rewrite pvertE //=.
rewrite inE => /orP[/eqP -> | ]; first by rewrite /left_limit; case : ifP.
by apply: Ih.
Qed.

Lemma opening_cells_seq_edge_shift p s c oe le he :
  {in oe, forall g, left_pt g == p} ->
  valid_edge le p -> valid_edge he p ->
  opening_cells_aux p oe le he = (s, c) ->
  le :: [seq high i | i <- rcons s c] =
  rcons [seq low i | i <- rcons s c] he.
Proof.
move=> + + vh.
elim: oe le s c => [ | g1 oe Ih] le s c leftg vl /=.
  by rewrite pvertE // pvertE // => -[] <- <- /=.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (leftg g1 _)) ?valid_edge_left // inE eqxx.
have leftg' : {in oe, forall g, left_pt g == p}.
  by move=> g gin; apply: leftg; rewrite inE gin orbT.
have := Ih _ _ _ leftg' vg1; case: (opening_cells_aux _ _ _ _)=> [s' c'].
move=> /(_ s' c' erefl) {}Ih.
by rewrite pvertE // => -  [] <- <- /=; congr (_ :: _).
Qed.

Lemma opening_cells_aux_subset c' s' c p s le he:
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  opening_cells_aux p s le he = (s', c') ->
  c \in rcons s' c' ->
  (low c \in le :: s) && (high c \in he :: s).
Proof.
move=> + vhe.
elim: s c' s' le => [ | g1 s Ih] c' s' le /= vle lsp.
rewrite pvertE // pvertE // => - [] <- <-.
by do 2 (case: ifP=> _); rewrite /= inE=> /eqP -> /=;
  rewrite !inE !eqxx.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (lsp g1 _)) ?valid_edge_left // inE eqxx.
have lsp' : {in s, forall g, left_pt g == p}.
  by move=> g gin; rewrite lsp // inE gin orbT.
have := Ih _ _ _ vg1 lsp'; case: (opening_cells_aux _ _ _ _)=> [s1 c1].
move=> /(_ _ _ erefl) {} Ih.
rewrite pvertE // => - [] <- <- /=; rewrite inE=> /orP[/eqP -> /= | ].
  by rewrite !inE ?eqxx ?orbT.
rewrite inE; move=>/Ih/andP[] ->; rewrite orbT andTb.
by rewrite !inE orbCA => ->; rewrite orbT.
Qed.


(*TODO : check all uses of opening_cells_aux_subset for potential uses
  of this simpler lemma. *)
Lemma opening_cells_subset c p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  c \in opening_cells p s le he ->
  (low c \in le :: s) && (high c \in he :: s).
Proof.
move=> vle vhe lsp.
rewrite /opening_cells.
case oca_eq : (opening_cells_aux _ _ _ _) => [so co] cin.
have lsp' : {in sort (@edge_below _) s, forall g, left_pt g == p}.
  by move=> g; rewrite mem_sort; apply: lsp.
have := opening_cells_aux_subset vle vhe lsp' oca_eq cin.
by rewrite !inE !mem_sort.
Qed.

(*
Lemma opening_cells_aux_nnil p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  opening_cells_aux p s le he != nil.
Proof.
by move=> + vhe; case: s => [ | g1 s] vle lsp; rewrite /= pvertE // ?pvertE.
Qed.
*)

Lemma opening_cells_aux_high p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  [seq high i | i <- (opening_cells_aux p s le he).1] = s.
Proof.
move=> vle vhe lsp.
elim: s le vle lsp => [ | g1 s Ih] le vle lsp.
  by rewrite /= pvertE // pvertE.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (lsp g1 _)) ?valid_edge_left // inE eqxx.
have lsp' : {in s, forall g, left_pt g == p}.
  by move=> g gin; apply: lsp; rewrite inE gin orbT.
rewrite /= pvertE //.
by have := Ih _ vg1 lsp'; case: (opening_cells_aux _ _ _ _) => [s' c'] /= ->.
Qed.

Lemma opening_cells_aux_high_last p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  high (opening_cells_aux p s le he ).2 = he.
Proof.
move=> + vhe; elim: s le => [ /= | g1 s Ih] le vle lsp.
  by rewrite pvertE // pvertE.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (lsp g1 _)) ?valid_edge_left // inE eqxx.
have lsp' : {in s, forall g, left_pt g == p}.
  by move=> g gin; apply: lsp; rewrite inE gin orbT.
have := Ih _ vg1 lsp'; rewrite /= pvertE //.
by case : (opening_cells_aux _ _ _ _) => [s' c'].
Qed.

Lemma opening_cells_high p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  [seq high i | i <- opening_cells p s le he] =
  rcons (sort (@edge_below R) s) he.
Proof.
move=> vle vhe lsp; rewrite /opening_cells.
have lsp' :
   {in sort (@edge_below _) s, forall g, left_pt g == p}.
  move=> g; rewrite mem_sort; apply: lsp.
move: (lsp') => /opening_cells_aux_high => /(_ _ _ vle vhe).
move: lsp' => /opening_cells_aux_high_last => /(_ _ _ vle vhe).
case: (opening_cells_aux _ _ _ _) => [s' c'] /=.
by rewrite map_rcons => -> ->.
Qed.

Lemma opening_cells_aux_right_form (ctxt s : seq edge) (p : pt) le he
 s' c' :
p >>= le -> p <<< he -> valid_edge le p -> valid_edge he p ->
le \in ctxt -> he \in ctxt ->
le <| he -> {in s, forall g, left_pt g == p} ->
{in ctxt &, (@no_crossing R)} ->
{subset s <= ctxt} ->
path (@edge_below R) le s  ->
opening_cells_aux p s le he = (s', c') ->
s_right_form (rcons s' c').
Proof.
move=> + ph + vh + hin + + noc + +.
elim: s le s' c' => [ | g1 edges IH] le s' c'
  pabove vle lin lowhigh outs allin sorted_e /=.
  by rewrite pvertE // pvertE // => -[] <- <- /=; rewrite andbT.
rewrite pvertE //.
have outs' : {in edges, forall g, left_pt g == p}.
  by move=> g gin; apply outs; rewrite inE gin orbT.
have allin' : {subset edges <= ctxt}.
  by move=> g gin; rewrite allin // inE gin orbT.
have sorted_e' : path (@edge_below R) g1 edges.
   by apply: (path_sorted sorted_e).
have /eqP gl : left_pt g1 == p by rewrite outs // inE eqxx.
have g1belowhigh : g1 <| he.
  have gin' : g1 \in ctxt by rewrite allin // inE eqxx.
  have/no_crossingE := noc g1 he gin' hin.
  by rewrite gl=>/(_ vh)=> -[]/(_ ph).
have pong : p === g1 by rewrite -gl left_on_edge.
have paboveg1 : p >>= g1
   by rewrite strict_nonAunder ?pong //; case/andP: pong.
move: (sorted_e) => /=/andP[] leg1 _.
have g1in : g1 \in ctxt by rewrite allin // inE eqxx.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (outs g1 _)) ?valid_edge_left // inE eqxx.
have := IH g1 _ _ paboveg1 vg1 g1in g1belowhigh outs' allin' sorted_e'.
case: (opening_cells_aux _ _ _ _) => [s1 c1] - /(_ _ _ erefl) {} IH /=.
by move=> [] <- <- /=; rewrite leg1.
Qed.

Lemma opening_cells_right_form p s low_e high_e :
valid_edge low_e p ->
valid_edge high_e p ->
p >>= low_e -> p <<< high_e ->
low_e <| high_e ->
{in s, forall g, left_pt g == p} ->
{in s, forall g, low_e <| g} ->
{in s, forall g, g <| high_e} ->
{in s &, (@no_crossing R)} ->
s_right_form (opening_cells p s low_e high_e).
Proof.
set mainsort := fun l => (perm_mem (permEl (perm_sort (@edge_below R) l))).
move=> vl vh pabove punder lowhigh outs alla allb noc; apply/allP.
have noc' : {in low_e :: high_e :: s &, (@no_crossing R)}.
  move=> e1 e2; rewrite !inE !orbA =>/orP[e1lh |e1in ]/orP[e2lh |e2in].
    by apply/orP;move:e1lh e2lh=> /orP[]/eqP -> /orP[]/eqP ->;
      rewrite ?edge_below_refl ?lowhigh ?orbT.
    - by move: e1lh=> /orP[]/eqP ->;apply/orP;
         rewrite/below_alt ?alla ?allb ?orbT.
    - by move: e2lh=> /orP[]/eqP ->; apply/orP;
         rewrite/below_alt ?alla ?allb ?orbT.
    by apply: noc.
have sorted_e : sorted (@edge_below R) (sort (@edge_below R) s).
  have /sort_sorted_in : {in low_e :: s &, total (@edge_below R)}.
    move=> e1 e2; rewrite !inE =>/orP[/eqP -> |e1in ]/orP[/eqP -> |e2in].
    - apply/orP; left; apply/orP; left; rewrite /point_under_edge.
      by rewrite (eqP (proj1 (pue_formula_two_points _ _)))
              (eqP (proj1 (proj2 (pue_formula_two_points _ _)))) !le_refl.
    - by rewrite alla.
    - by rewrite alla ?orbT.
    - by apply/orP/noc.
  by apply; apply/allP=> x xin /=; apply/orP; right; exact: xin.
have /sub_in1/= trsf : {subset sort (@edge_below R) s <= s}.
  by move=> x; rewrite mainsort.
move/trsf:outs => {}outs.
have [lin hin] : (low_e \in [:: low_e, high_e & s]) /\
   (high_e \in [:: low_e, high_e & s]).
  by split; rewrite !inE eqxx ?orbT.
have slho : {subset (sort (@edge_below _) s) <=
               [:: low_e, high_e & s]}.
  by move=> x; rewrite mainsort => xin; rewrite !inE xin ?orbT.
move=> x xin.
have srt : sorted (@edge_below R) (low_e :: sort (@edge_below R) s).
  case sq : (sort (@edge_below R) s) => [// | a tl].
    rewrite -[sorted _ _]/((low_e <| a) && sorted (@edge_below R) (a :: tl)).
    by rewrite -sq sorted_e andbT alla // -mainsort sq inE eqxx.
have := (opening_cells_aux_right_form _ _ _ _ lin hin lowhigh outs).
move: xin; rewrite /opening_cells.
case: (opening_cells_aux _ _ _ _) => [s1 c1] xin - /(_ s1 c1).
move=> /(_ _ _ _ _ _ _ _ erefl) => it.
by apply: (allP (it _ _ _ _ _ _ _) x xin).
Qed.

Lemma lower_edge_new_cells e low_e high_e:
forall new_open_cells,
valid_edge low_e (point e) ->
valid_edge high_e (point e) ->
opening_cells (point e) (outgoing e) low_e high_e = new_open_cells ->
(low (head dummy_cell new_open_cells) == low_e).
Proof.
move=> vle vhe.
rewrite /opening_cells.
case : (sort (@edge_below R) (outgoing e)) => [/= |/= c q] newop.
  by rewrite pvertE // pvertE //= => <- /=.
rewrite pvertE //.
by case: (opening_cells_aux _ _ _ _) => [s1 c1] /= => <- /=.
Qed.

Lemma opening_cells_not_nil out le he p :
  opening_cells p out le he != [::].
Proof.
rewrite /opening_cells; case: (opening_cells_aux _ _ _ _) => [s1 c1].
apply/eqP/rcons_neq0.
Qed.

Lemma higher_edge_new_cells e low_e high_e:
out_left_event e ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
forall new_open_cells,
opening_cells (point e) (outgoing e) low_e high_e =
   new_open_cells ->
(high (last dummy_cell new_open_cells) == high_e).
Proof.
rewrite /opening_cells.
move=> /outleft_event_sort outl vle vhe.
have := opening_cells_aux_high_last vle vhe outl.
case : (opening_cells_aux _ _ _ _) => [s1 c1] <- ? <-.
by rewrite last_rcons.
Qed.

Lemma opening_cells_close event low_e high_e future :
valid_edge low_e (point event) ->
valid_edge high_e (point event) ->
out_left_event event ->
end_edge low_e future -> end_edge high_e future ->
close_out_from_event event future ->
close_alive_edges (opening_cells (point event) (outgoing event) low_e high_e)
   future.
Proof.
rewrite /opening_cells.
move=> vle vhe oute A B /close_out_from_event_sort; move: A B.
have : {in sort (@edge_below _) (outgoing event),
          forall g, left_pt g == (point event)}.
  by move=> g; rewrite mem_sort; apply: oute.
move : low_e vle.
elim : (sort (@edge_below R) (outgoing event)) => [| g1 q Ih] /= 
            le vle oute' endl endh.
  move=> _.
  by rewrite pvertE // pvertE //= endl endh.
move => /andP[] endg1 allend.
have oute1 : {in q, forall g, left_pt g == point event}.
  by move=> g gin; apply oute'; rewrite inE gin orbT.
have vg1 : valid_edge g1 (point event).
  by rewrite -(eqP (oute' g1 _)) ?valid_edge_left // inE eqxx.
have:= Ih g1 vg1 oute1 endg1 endh allend.
case : (opening_cells_aux _ _ _ _) => [s1 c1] => {}Ih.
by rewrite pvertE //= endl endg1 Ih.
Qed.

Lemma higher_lower_equality e open :
out_left_event e ->
forall first_cells (contact_cells : seq cell) (last_contact : cell)
  last_cells low_e high_e,
open_cells_decomposition open (point e) =
(first_cells, contact_cells, last_contact, last_cells, low_e, high_e) ->
forall new_cells,
(opening_cells (point e) (outgoing e) low_e high_e) = new_cells ->
(exists2 c : cell, c \in open & contains_point' (point e) c) ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
low (head last_contact contact_cells) = low (head dummy_cell new_cells) /\
high last_contact = high (last dummy_cell new_cells).
Proof.
move => outleft fc cc lcc lc lowe highe oe new_cells op_new exi lowv highv.
have := (lower_edge_new_cells lowv highv op_new) => /eqP low_new.
have := (higher_edge_new_cells outleft lowv highv op_new) => /eqP high_new.
have [ _ [_ [_ [_ [_ [heq [leq _]]]]]]]:=
  open_cells_decomposition_main_properties oe exi.
by rewrite low_new high_new leq heq.
Qed.

Lemma opening_valid e low_e high_e:
out_left_event e ->
valid_edge low_e (point e) ->
valid_edge high_e (point e) ->
seq_valid (opening_cells (point e) (outgoing e) low_e high_e) (point e).
Proof.
move=> + + vhe.
rewrite /opening_cells.
move/outleft_event_sort.
move : low_e.
elim : (sort (@edge_below R) (outgoing e)) => [/= | c q IH] low_e outl vle.
  rewrite /=.
  by rewrite pvertE // pvertE //= vle vhe.
rewrite /=.
rewrite pvertE //.
have vc : valid_edge c (point e).
  by rewrite -(eqP (outl c _)) ?valid_edge_left // inE eqxx.
have outl1 : forall g, g \in q -> left_pt g == point e.
  by move=> g gin; rewrite outl // inE gin orbT.
have := IH c outl1 vc.
case: (opening_cells_aux _ _ _ _) => [s1 c1] {} Ih /=.
by rewrite vle vc Ih.
Qed.

Lemma adjacent_opening_aux' p s le he news newc :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  opening_cells_aux p s le he = (news, newc) -> 
  adjacent_cells (rcons news newc) /\
   (low (head dummy_cell (rcons news newc)) = le).
Proof.
move=> + vhe.
elim: s le news newc => [ | g s Ih] le news newc /= vle oute.
  by rewrite pvertE // pvertE // => - [] <- <- /=.
have vg : valid_edge g p.
  by rewrite -(eqP (oute g _)) ?valid_edge_left // inE eqxx.
have oute' : {in s, forall g, left_pt g == p}.
  by move=> g' gin; rewrite oute // inE gin orbT.
case oca_eq: (opening_cells_aux _ _ _ _) => [s1 c1].
have := Ih g s1 c1 vg oute' oca_eq => -[] Ih1 Ih2 {Ih}.
  rewrite pvertE // => - [] <- <- /=; split;[ | done].
case: (s1) Ih1 Ih2 => [ | a s'] /=.
  by move=> _ ->; rewrite eqxx.
by move=> -> ->; rewrite eqxx.
Qed.

Lemma adjacent_opening' p s le he:
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  adjacent_cells (opening_cells p s le he).
Proof.
move=> vle vhe lefts.
have lefts' : {in sort (@edge_below _) s, forall g, left_pt g == p}.
  by move=> g; rewrite mem_sort; apply: lefts.
rewrite /opening_cells; case oca_eq: (opening_cells_aux _ _ _ _) => [so co].
by have [] := adjacent_opening_aux' vle vhe  lefts' oca_eq.
Qed.

Lemma opening_cells_last_lexePt e low_e high_e c :
out_left_event e ->
~~(point e <<< low_e) -> point e <<< high_e ->
valid_edge low_e (point e)-> valid_edge high_e (point e) ->
{in  (rcons (low_e::(sort (@edge_below R) (outgoing e))) high_e) &, no_crossing R} ->
low_e <| high_e ->
 c \in (opening_cells (point e) (outgoing e) low_e high_e) ->
 lexePt (last dummy_pt (left_pts c)) (point e).
Proof.
rewrite /opening_cells.
move => /outleft_event_sort outlefte eabl eunh lowv highv .
elim : (sort (@edge_below R) (outgoing e)) low_e eabl lowv outlefte => [/= | c' q IH] low_e eabl lowv outlefte nc linfh.
  have := pvertE highv; set high_p := Bpt _ _ => hp.
  have := pvertE lowv; set low_p := Bpt _ _ => lp.
  have := intersection_on_edge lp=> [][] poel lx_eq.
  have := intersection_on_edge hp=> [][] poeh hx_eq.
  rewrite lp hp.
  rewrite lx_eq in hx_eq.
  have y_ineq := order_below_viz_vertical lowv highv lp hp linfh.
  rewrite  inE => /eqP -> /=.
  case : ifP => [/eqP <-/=|/= _].
    case : ifP=> [/eqP <-/=|/= _].
      by rewrite /lexePt eqxx le_refl orbT .
    by rewrite /lexePt hx_eq eqxx y_ineq /= orbT.
  rewrite /lexePt /=.
  case : ifP => [/eqP <-/=|/=_ ].
    by rewrite eqxx le_refl /= orbT.
  rewrite lx_eq eqxx.
  have -> : p_y low_p <= p_y (point e).
    by rewrite leNgt -(strict_under_edge_lower_y lx_eq poel).
  by rewrite orbT.
rewrite /= .
have cin : c' \in c' :: q.
  by rewrite  inE eqxx.
have c'v: (valid_edge c' (point e)).
  apply valid_edge_extremities.
  by rewrite outlefte // cin.
have einfc' : ~~ (point e <<< c').
  apply : onAbove.
  have := outlefte c' cin => /eqP <-.
  apply :  left_on_edge.
have outq: (forall e0 : edge_eqType R, e0 \in q -> left_pt e0 == point e).
  move => e0 ein.
  apply outlefte.
  by rewrite inE ein orbT.
have c'infh : c' <| high_e.
  have := nc high_e c'.
  rewrite /= !inE  !mem_rcons !inE  !eqxx !orbT /= => /(_ isT isT).
  move=> /below_altC/no_crossingE.
  have := outlefte c' cin => /eqP ->.
  rewrite highv eunh => [] /(_ isT) [a _].
  by apply: a.
have nc' : {in  (rcons (c'::q) high_e) &, no_crossing R}.
  move => e1 e2 e1in e2in.
  apply nc.
    by rewrite inE e1in orbT.
  by rewrite inE e2in orbT.
have := pvertE lowv; set low_p := Bpt _ _ => lp.
rewrite lp.
have := intersection_on_edge lp=> [][] poel lx_eq.
case oca_eq : (opening_cells_aux _ _ _ _) => [so co].
case : ifP=> [/eqP <-/=|/= _].
  rewrite inE => /orP  [/eqP -> /=|].
    by rewrite lexePt_refl.
  have := IH c' einfc' c'v outq nc' c'infh.
  by rewrite oca_eq.
rewrite inE => /orP  [/eqP -> /=|].
  have : p_y low_p <= p_y (point e).
    by rewrite leNgt -(strict_under_edge_lower_y lx_eq poel).
  rewrite /lexePt lx_eq eqxx=> ->.
  by rewrite orbT.
have := IH c' einfc' c'v outq nc' c'infh.
by rewrite oca_eq.
Qed.

Lemma opening_cells_aux_side_limit e s le he s' c':
  valid_edge le e -> valid_edge he e -> le <| he ->
  e >>= le -> e <<< he ->
  {in [:: le, he & s] &, no_crossing R} ->
  {in s, forall g, left_pt g == e} ->
  opening_cells_aux e s le he = (s', c') ->
  all open_cell_side_limit_ok (rcons s' c').
Proof.
move=> + vh.
elim : s le s' c'=> [ | g s Ih] le s' c' /= vl lowhigh above under noc lg.
  have := pvertE vl; set p1 := Bpt _ _ => /[dup] vip1 ->.
  have := pvertE vh; set p2 := Bpt _ _ => /[dup] vip2 ->.
  rewrite /open_cell_side_limit_ok => -[] <- <- /=.
  have [v1 on1 x1] : [/\ valid_edge le p1, p1 === le & p_x e = p_x p1].
    by have [on1 xp] := intersection_on_edge vip1.
  have [v2 on2 x2] : [/\ valid_edge he p2, p2 === he & p_x e = p_x p2].
    by have [on2 xp] := intersection_on_edge vip2.
  have p2ne : p2 != e.
    apply/eqP=> A; have := strict_under_edge_lower_y x2 on2.
    by rewrite under => /esym; rewrite ltNge A lexx.
  rewrite (negbTE p2ne); case: ifP => [p1ise | p1ne] /=;
    move: on1 on2; rewrite ?(eqP p2ise) -?(eqP p1ise) => on1 on2;
    rewrite ?eqxx ?on1 ?on2 ?(eqP p2ise) -?(eqP p1ise) -?x1 -?x2
        ?eqxx ?andbT //=.
    have euh : e <<= he.
      apply: (order_edges_viz_point' vl)=> //.
      move: on1; rewrite /point_on_edge /point_under_edge=>/andP[]/eqP -> _.
      by rewrite lexx.
    rewrite lt_neqAle.
    have tmp:= (under_edge_lower_y x2 on2).
    rewrite (eqP p1ise) /p1 /p2 /= in tmp; rewrite -tmp {tmp}.
    rewrite -/p1 -(eqP p1ise) euh andbT.
    apply/negP=> A; case/negP: p2ne; rewrite pt_eqE (eqP p1ise) /=.
    by rewrite (eqP A) !eqxx.
  rewrite -(strict_under_edge_lower_y x2 on2) under /=.
  rewrite ltNge le_eqVlt negb_or.
  rewrite -(strict_under_edge_lower_y x1 on1) above andbT.
  by apply/negP=> A;case/negbT/negP:p1ne; rewrite pt_eqE -?x1 (eqP A) !eqxx.
have /eqP lgg : left_pt g == e by apply: lg; rewrite inE eqxx.
have := pvertE vl; set p1 := Bpt _ _ => /[dup] vip1 ->.
have [v1 on1 x1] : [/\ valid_edge le p1, p1 === le & p_x e = p_x p1].
  by have [on1 xp] := intersection_on_edge vip1.
have eong : e === g by rewrite -(eqP (lg g _)) ?inE ?eqxx // left_on_edge.
case oca_eq : (opening_cells_aux _ _ _ _) => [so co] [] <- <-.
rewrite /=; apply/andP; split.
  rewrite /open_cell_side_limit_ok.
  case: ifP=> [eisp1 | enp1] /=;
    rewrite -?x1 !eqxx on1 -?(eqP eisp1) ?eong ?andbT //=.
  rewrite ltNge le_eqVlt negb_or.
  rewrite -(strict_under_edge_lower_y x1 on1) above andbT.
  by apply/negP=> A; case/negP: enp1; rewrite pt_eqE (eqP A) x1 ?eqxx.
apply/allP=> c cintl.
suff/allP/(_ c cintl) : all open_cell_side_limit_ok (rcons so co) by [].
apply: (Ih g) => //.
- by apply: valid_edge_extremities; rewrite lg ?inE ?eqxx.
- have [hein gin] : he \in [:: le , he, g & s] /\ g \in [:: le, he, g & s].
    by split; rewrite !inE eqxx ?orbT.
  have := no_crossingE (noc _ _ gin hein).
  rewrite (eqP (lg _ _)); last by rewrite inE eqxx.
  by move=> /(_ vh) [] /(_ under).
- by rewrite -(eqP (lg g _)) ?inE ?eqxx ?left_pt_above.
- move: noc; apply: sub_in2.
  by move=> g'; rewrite !inE => /orP [-> |/orP[-> | ->]]; rewrite ?orbT.
by move: lg; apply: sub_in1 => g' gin; rewrite inE gin orbT.
Qed.

Lemma opening_cells_side_limit e s le he :
  valid_edge le e -> valid_edge he e -> le <| he ->
  e >>= le -> e <<< he ->
  {in [:: le, he & s] &, no_crossing R} ->
  {in s, forall g, left_pt g == e} ->
  all open_cell_side_limit_ok (opening_cells e s le he).
Proof.
move=> vle vhe bel ea eu noc lefts.
have lefts' : {in sort (@edge_below _) s, forall g, left_pt g == e}.
  by move=> g; rewrite mem_sort; apply: lefts.
have := opening_cells_aux_side_limit vle vhe bel ea eu _ lefts'.
rewrite /opening_cells.
case oca_eq : (opening_cells_aux _ _ _ _) => [so co].
apply=> //.
move=> g1 g2; rewrite !inE !(perm_mem (permEl (perm_sort _ _)))=> g1in g2in.
by apply: noc.
Qed.

Lemma opening_cells_below_high p e c s le he:
  le <| he ->
  (e >>> le) && (e <<< he) ->
  valid_edge le e ->
  valid_edge he e ->
  valid_edge he p -> (forall g, g \in s -> left_pt g == e) ->
  {in le::he::s &, no_crossing R} ->
  c \in opening_cells e s le he -> strict_inside_open p c -> p <<< he.
Proof.
move=> lowhigh ebounds vle vhe vp gleft noc oc /andP[]/andP[] plhc _ lims.
move: (ebounds) => /andP[] above under.
have labove : e >>= le by rewrite -leNgt ltW // ltNge; exact: above.
have := opening_cells_subset vle vhe gleft oc => /andP[] _.
rewrite inE=>/orP[/eqP <- //|hcin].
have hcin' : high c \in le :: he :: s by rewrite !inE hcin ?orbT.
have hein : he \in le :: he :: s by rewrite !inE eqxx !orbT.
have blo : high c <| he.
  have := no_crossingE (@noc _ _ hcin' hein).
  rewrite (eqP (gleft _ hcin)) vhe.
  by move: ebounds=> /andP[] _ -> /(_ isT)[] /(_ isT).
apply: (order_edges_strict_viz_point' _ vp blo plhc).
have cok := opening_cells_side_limit vle vhe lowhigh labove under noc gleft.
move: cok =>/allP/(_ c oc) {}cok.
by apply: (valid_high_limits cok); move: lims=> /andP[] -> /ltW ->.
Qed.

Lemma opening_cells_above_low p e c s le he:
  le <| he ->
  (e >>> le) && (e <<< he) ->
  valid_edge le e ->
  valid_edge he e ->
  valid_edge le p -> (forall g, g \in s -> left_pt g == e) ->
  {in le:: he :: s &, no_crossing R} ->
  c \in opening_cells e s le he -> strict_inside_open p c -> p >>> le.
Proof.
move=> lowhigh ebounds vle vhe vp gleft noc oc /andP[]/andP[] _ palc lims.
move: (ebounds) => /andP[] above under.
have labove : e >>= le by rewrite -leNgt ltW // ltNge; exact: above.
have := opening_cells_subset vle vhe gleft oc => /andP[] + _.
rewrite inE=>/orP[/eqP <- //|lcin].
have lcin' : low c \in le :: he :: s by rewrite !inE lcin !orbT.
have lein : le \in le :: he :: s by rewrite !inE eqxx.
have blo : le <| low c.
  have := no_crossingE (@noc _ _ lcin' lein).
  rewrite (eqP (gleft _ lcin)) vle.
  by move: ebounds=> /andP[] -> _ /(_ isT)[] _ /(_ isT).
apply/negP=> pule; case/negP: palc.
apply: (order_edges_viz_point' vp _ blo pule).
have cok := opening_cells_side_limit vle vhe lowhigh labove under noc gleft.
move: cok => /allP/(_ c oc) {}cok.
by apply: (valid_low_limits cok); move: lims=> /andP[] -> /ltW ->.
Qed.

Lemma opening_cells_aux_disjoint (s oe : seq edge) p le he s' c' :
    p >>> le -> p <<< he -> le \in s -> he \in s -> le <| he ->
    valid_edge le p -> valid_edge he p -> {subset oe <= s} ->
    {in s &, no_crossing R} -> {in oe, forall g : edge, left_pt g == p} ->
    path (@edge_below R) le oe ->
    opening_cells_aux p oe le he = (s', c') ->
    {in rcons s' c' &, disjoint_open_cells R}.
Proof.
move=> pl ph lein hein lowhigh vl vh oesub noc leftg soe.
have {}pl : p >>= le by apply/negP=> pule; case/negP: pl; apply: underW.
elim: oe s' c' oesub leftg le lowhigh pl lein vl soe
   => [ | og oe Ih] s' c' oesub leftg le lowhigh pl lein vl soe /=.
  have := pvertE vl; set p1 := Bpt _ _ => /[dup] vip1 ->.
  have := pvertE vh; set p2 := Bpt _ _ => /[dup] vip2 -> [] <- <- /=.
  by move=> c1 c2; rewrite !inE /= => /eqP -> /eqP ->; left.
have := pvertE vl; set p1 := Bpt _ _ => /[dup] vip ->.
set W := Bcell _ _ _ _.
case oca_eq : (opening_cells_aux _ _ _ _) => [so co] [] <- <-.
have /eqP logp : left_pt og == p by apply/leftg; rewrite inE eqxx.
suff main : forall c, c \in rcons so co -> o_disjoint_e W c.
  move=> c1 c2; rewrite !inE => /orP[/eqP c1W |c1in] /orP[/eqP c2W | c2in].
  - by left; rewrite c1W c2W.
  - by rewrite c1W; apply: main.
  - by rewrite c2W; apply/o_disjoint_eC/main.
have oesub' : {subset oe <= s}.
  by move=> x xin; rewrite oesub // inE xin orbT.
have leftg' : {in oe, forall g, left_pt g == p}.
  by move=> x xin; rewrite leftg // inE xin orbT.
have ogbh : og <| he.
  have ogin : og \in s by rewrite oesub // inE eqxx.
  have := no_crossingE (noc _ _  ogin hein); rewrite logp vh ph.
  by move=> /(_ isT)[]/(_ isT).
have paog : p >>= og.
  by rewrite -(eqP (leftg og _)) ?left_pt_above // inE eqxx.
have ogins : og \in s.
  by rewrite oesub // inE eqxx.
have vog : valid_edge og p.
  by rewrite valid_edge_extremities // leftg ?inE ?eqxx.
have soe' : path (@edge_below _) og oe.
  by move: soe=> /=/andP[] _.
by apply: (Ih so co oesub' leftg' og ogbh paog ogins vog soe' oca_eq).
move=> c cin; right=> q.
have oc0q : opening_cells_aux p (og :: oe) le he = (W :: so, co).
  by rewrite /= oca_eq pvertE.
have noc' : {in [:: le, he , og & oe] &, no_crossing R}.
  move: noc; apply: sub_in2 => g; rewrite 2!inE.
  by move=> /orP[/eqP ->| /orP[/eqP -> | ginoe]] //; apply: oesub.
have /allP cok :=
   opening_cells_aux_side_limit vl vh lowhigh pl ph noc' leftg oc0q.
have [ | qnW//] :=  boolP(inside_open' q W).
  move=> /andP[]/andP[] /andP[] _ Main2 /andP[] _ w2 /andP[] Main1 w1/=.
have vhwq : valid_edge (high W) q.
  apply: valid_high_limits; last by rewrite w1 w2.
  by apply: cok; rewrite mem_rcons !inE eqxx orbT.
have [adj0 _] := adjacent_opening_aux' vl vh leftg oc0q.
have rf0 := opening_cells_aux_right_form pl ph vl vh lein hein lowhigh
   leftg noc oesub soe oc0q.
have := seq_edge_below' adj0 rf0; rewrite [head _ _]/= => srt.
have vog : valid_edge og q by move: vhwq; rewrite [high W]/=.
set c0 := head W (rcons so co).
have ogl : og = low c0.
  by move: adj0; rewrite /c0; case: (so) => [ | {}c0 s0] /= /andP[/eqP ] .
move: vog; rewrite ogl=> vog.
move: (cin) => /(nthP W) [rank rltsize /esym ceq].
case rankeq: rank => [ | rank'].
  have cc0 : c = c0 by rewrite ceq rankeq.
  rewrite cc0 /inside_open'/inside_open_cell/contains_point -ogl.
  by move: Main2; rewrite /= => ->; rewrite ?andbF.
apply/negP; rewrite /inside_open'/inside_open_cell => inc.
have valq : valid_edge (low c) q.
  apply: valid_low_limits.
    by apply: cok; rewrite /= inE cin orbT.
  by move: inc=> /andP[] /andP[] _ /andP[] _ -> /andP[] _ ->.
have leftg' : {in oe, forall g, left_pt g == p}.
  by move: leftg; apply: sub_in1=> g' gin; rewrite inE gin orbT.
have tr : {in (og :: oe) & & , transitive (@edge_below R)}.
  apply: (@edge_below_trans R p); last by move: noc; apply: sub_in2.
    by left; move=> g gin; rewrite -(eqP (leftg g gin)) edge_cond.
  by move=> g gin; apply: valid_edge_extremities; rewrite leftg ?eqxx.
have vog' : valid_edge og p.
  by rewrite valid_edge_extremities // (leftg og) ?inE ?eqxx.
have  allid : all (mem (og :: oe)) [seq low i | i <- rcons so co].
  apply/allP=> g /mapP [c2 c2p1 ->].
  by have := opening_cells_aux_subset vog' vh leftg' oca_eq c2p1 => /andP[].
have hWblc : high W <| low c.
  case soq : so => [ | c0' so'].
    by move: rltsize; rewrite soq rankeq /=.
  move: allid; rewrite soq [map _ _]/==> allid.
  have := path_sorted_inE tr allid.
  move: srt; rewrite [map _ _]/=.
  rewrite (opening_cells_seq_edge_shift leftg' vog' vh oca_eq).
  rewrite soq /= => /andP[] lec0; rewrite map_rcons rcons_path => /andP[] -> A.
  move=> /esym/andP[] cmpc0 _.
  rewrite ogl /c0 soq /=.
  move: cin; rewrite mem_rcons soq !inE orbA=>/orP[/orP[]/eqP -> | ].
      by apply: (allP cmpc0); rewrite -map_rcons map_f // mem_rcons inE eqxx.
    by rewrite edge_below_refl.
  move=> cin; apply: (allP cmpc0); rewrite -map_rcons map_f //.
  by rewrite mem_rcons inE cin orbT.
have qu:= order_edges_viz_point' vhwq valq hWblc Main2.
by move: inc; rewrite qu !andbF.
Qed.

End opening_cells.

Lemma open_cells_decomposition_cat f l p :
   adjacent_cells (f ++ l) ->
   s_right_form (f ++ l) ->
   seq_valid (f ++ l) p ->
   (exists2 c, c \in l & contains_point' p c) ->
   p >>> low (head dummy_cell l) ->
   let '(fc', cc, lcc, lc, le, he) :=
     open_cells_decomposition l p in
   open_cells_decomposition (f ++ l) p =
     (f ++ fc', cc, lcc, lc, le, he).
Proof.
move=> + + + exi pal.
elim: f => [ | c0 f Ih].
  move=> adj rfo sval.
 by case: (open_cells_decomposition l p) => [[[[[fc cc] lcc] lc] le] he].
rewrite /= => adj /andP[] lbh0 rfo /andP[] /andP[] vlc0 vhc0 sval.
case ocal_eq : (open_cells_decomposition l p) =>
  [[[[[fc' cc'] lcc'] lc'] le'] he'].
case oca_eq : (open_cells_decomposition _ _) =>
  [[[[[fc1 cc1] lcc1] lc1] le1] he1].
have exi0 : exists2 c, c \in c0 :: f ++ l & contains_point' p c.
  by case: exi => c cin A; exists c=> //; rewrite inE mem_cat cin !orbT.
have := open_cells_decomposition_main_properties oca_eq exi0 =>
  -[ocd [lcc_ctn [allct [allnct [flnct [heq [leq [lein hein]]]]]]]].
have := open_cells_decomposition_main_properties ocal_eq exi =>
  -[ocd' [lcc_ctn' [allct' [allnct' [flnct' [heq' [leq' [lein' hein']]]]]]]].
have svalf : seq_valid f p.
  by apply/allP=> x xin; apply: (allP sval); rewrite mem_cat xin.
have rfof : s_right_form f.
  by apply/allP=> x xin; apply: (allP rfo); rewrite mem_cat xin.
have adjf : adjacent_cells f.
  by move: adj; rewrite cat_path=> /andP[] /path_sorted.
have hfq : high (last c0 f) = low (head dummy_cell l).
  case: (l) adj exi => [ | c1 l']; first by move => _ [].
  by rewrite cat_path /==> /andP[] _ /andP[] /eqP.
move: oca_eq; rewrite /open_cells_decomposition /=.
case: ifP=> [c0ctn | c0nctn].
  move: c0ctn; rewrite /contains_point -[X in _ && X]negbK.
  have [/eqP f0 | fn0] := boolP (f == nil).
    by move: hfq; rewrite f0 /= => ->; rewrite pal andbF.
  have := above_all_cells svalf adjf rfof.
  have -> : high (last dummy_cell f) = high (last c0 f).
    by case: (f) fn0.
  rewrite hfq pal=> /(_ isT) [] palf _.
  have -> : high c0 = low (head dummy_cell f).
    by move: adj fn0; case: (f) => [// | ? ?] /= /andP[] /eqP.
  by rewrite palf andbF.
move: ocal_eq; rewrite /open_cells_decomposition.
case ocal_eq: (open_cells_decomposition_rec _ _) =>
  [[[fc2 cc2] lcc2] lc2] [] <- <- <- <- <- <-.
have adj' : adjacent_cells (f ++ l).
  by move: adj=> /path_sorted.
have := Ih adj' rfo sval; rewrite /open_cells_decomposition.
rewrite ocal_eq.
case: (open_cells_decomposition_rec (f ++ l) p) => [[[fc4 cc4] lcc4] lc4].
by move=> -[] -> -> -> -> _ _ [] <- <- <- <- <- <-.
Qed.

Lemma open_cells_decomposition_cat' f l p :
  adjacent_cells (f ++ l) ->
  s_right_form (f ++ l) ->
  seq_valid (f ++ l) p ->
  (exists2 c, c \in (f ++ l) & contains_point' p c) ->
  f != nil ->
  p >>> high (last dummy_cell f) ->
   let '(fc', cc, lcc, lc, le, he) :=
     open_cells_decomposition l p in
   open_cells_decomposition (f ++ l) p =
     (f ++ fc', cc, lcc, lc, le, he).
Proof.
move=> adj rfo sval [w win wctn] fnnil paf.
have adjf : adjacent_cells f by move: adj=> /adjacent_catW[].
have rfof : s_right_form f.
  by apply/allP=> x xin; apply: (allP rfo); rewrite mem_cat xin.
have svalf : seq_valid f p.
  by apply/allP=> x xin; apply: (allP sval); rewrite mem_cat xin.
have winl : w \in l.
  have [_ abaf] := above_all_cells svalf adjf rfof paf.
  have wnf : w \notin f.
    apply/negP=> abs.
    by move: wctn; rewrite /contains_point' -[X in _ && X]negbK abaf ?andbF //.
  by move: win; rewrite mem_cat (negbTE wnf).
have exi' : exists2 c, c \in l & contains_point' p c by exists w.
have hfq : high (last dummy_cell f) = low (head dummy_cell l).
  move: adj fnnil; case: (f) => [ // | c0 f']; rewrite /= cat_path=> /andP[] _ + _.
  by move: winl; case: (l) => [ // | c1 l'] _ /= /andP[] /eqP.
by apply: open_cells_decomposition_cat; rewrite // -hfq.
Qed.

Section step.


Variable e : event.
Variable fop : seq cell.
Variable lsto : cell.
Variable lop : seq cell.
Variable cls : seq cell.
Variable lstc :  cell.
Variable lsthe : edge.
Variable lstx : R.
Variable future_events : seq event.
Variable p : pt.

Let open := (fop ++ lsto :: lop).
(* There is almost no guarantee where lsto is with respect to the next event. *)
(* It is only guaranteed to be the highest of the last created cells. *)

Hypothesis inbox_e : inside_box (point e).
Hypothesis inbox_es : all inside_box [seq point x | x <- future_events].
Hypothesis oute : out_left_event e.
Hypothesis rfo : s_right_form open.
Hypothesis cbtom : cells_bottom_top open.
Hypothesis adj : adjacent_cells open.
Hypothesis sval : seq_valid open (point e).
Hypothesis cle : close_edges_from_events (e :: future_events).
Hypothesis clae : close_alive_edges open (e :: future_events).
Hypothesis lstheq : lsthe = high lsto.
Hypothesis lstheqc : lsthe = high lstc.
Hypothesis lstxq : lstx = left_limit lsto.
Hypothesis abovelstle :
  p_x (point e) = lstx -> (point e) >>> low lsto.
Hypothesis elexp : lexePt (point e) p.
Hypothesis plexfut : {in future_events, forall e', lexePt p (point e')}.
Hypothesis inbox_p : inside_box p.
Hypothesis noc : {in all_edges open (e :: future_events) &, no_crossing R}.
Hypothesis gs : edge_side  (e :: future_events) open.
Hypothesis sort_evs : path (@lexPtEv _) e future_events.

Let subo : {subset outgoing e <= all_edges open (e :: future_events)}.
Proof.
move=> x xo.
rewrite mem_cat /events_to_edges; apply/orP; right.
apply/flattenP; exists (outgoing e)=> //.
by apply: map_f; rewrite inE eqxx.
Qed.

Let subo' : {subset sort (@edge_below _) (outgoing e)
                 <= all_edges open (e :: future_events)}.
Proof.
by move=> x; rewrite mem_sort=> xo; apply: subo.
Qed.

Let exi : exists2 c, c \in open & contains_point' (point e) c.
Proof. by apply: (exists_cell cbtom adj (inside_box_between inbox_e)). Qed.

Let exi' : point e >>> lsthe ->
  exists2 c, c \in lop & contains_point' (point e) c.
Proof.
rewrite lstheq; move=> pa.
suff abf : {in fop, forall c, point e >>> high c}.
have [wc wcin wcct] := exi; exists wc => //.
  move: wcin; rewrite /open !(mem_cat, inE) => /orP[wf | /orP[/eqP wl | //]].
    by move: wcct; rewrite /contains_point' (negbTE (abf _ wf)) andbF.
  by move: wcct; rewrite /contains_point' wl (negbTE pa) andbF.
have vfop1 : seq_valid (rcons fop lsto) (point e).
  apply/allP=> x xin; apply: (allP sval).
  by  rewrite /open -cat_rcons mem_cat xin.
have vfop : {in rcons fop lsto, forall c, valid_edge (high c) (point e)}.
  move=> c cin.
  have cin' : high c \in [seq high i | i <- open].
    by apply: map_f; rewrite /open -cat_rcons mem_cat cin.
  by apply: (seq_valid_high sval cin').
have rfop : s_right_form (rcons fop lsto).
  apply/allP=> x xin; apply: (allP rfo x).
  by rewrite /open -cat_rcons mem_cat xin.
have afop : adjacent_cells (rcons fop lsto).
  by move: adj; rewrite /open -cat_rcons => /adjacent_catW [].
have vh : valid_edge (low (head lsto fop)) (point e).
  by move: sval; rewrite /open; case: (fop) => [ | ? ?] /= /andP[] /andP[].
suff [] : point e >>> low (head lsto fop) /\
       {in fop, forall c, point e >>> high c} by [].
have := above_all_cells vfop1 afop rfop; rewrite last_rcons=> /(_ pa).
have hq : head dummy_cell (rcons fop lsto) = head lsto fop.
  by case: (fop) => [ | ? ?].
rewrite hq => -[-> others]; split=> // x xin.
by apply: others; rewrite mem_rcons inE xin orbT.
Qed.

Let lstoin : lsto \in open.
Proof. by rewrite !(mem_cat, inE) eqxx orbT. Qed.

Definition state_open_seq (s : scan_state) :=
  sc_open1 s ++ lst_open s :: sc_open2 s.

Definition invariant1 (s : scan_state) :=
  close_alive_edges (state_open_seq s) future_events /\
  seq_valid (state_open_seq s) p /\
  adjacent_cells (state_open_seq s) /\
  cells_bottom_top (state_open_seq s) /\
  s_right_form (state_open_seq s).

Let val_between g (h : valid_edge g (point e)) := 
  valid_between_events elexp plexfut h inbox_p.

Lemma default_case ncs lnc lh lx:
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) :=
      opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
  invariant1
    {| sc_open1 := fc ++ nos;
       lst_open := lno;
       sc_open2 := lc;
       sc_closed := ncs;
       lst_closed := lnc;
       lst_high := lh;
       lst_x := lx|}.
Proof.
case oe : (open_cells_decomposition open (point e)) =>
 [[[[[fc cc] lcc] lc] le] he].
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    open_cells_decomposition_main_properties oe exi.
have [pal puh vle vhe ncont] :=
    decomposition_connect_properties rfo sval adj cbtom 
            (inside_box_between inbox_e) oe.
case oca_eq:(opening_cells_aux _ _ _ _) => [nos nlsto].
rewrite /invariant1 /state_open_seq /=.
have dec_not_end :=
    decomposition_not_end rfo sval adj cbtom 
          (inside_box_between inbox_e) oe.
have close_fc : close_alive_edges fc future_events.
  suff/head_not_end : close_alive_edges fc (e :: future_events).
    by apply=> c0 cin; apply: dec_not_end; rewrite cin.
  by apply/allP=> c0 cin; apply: (allP clae); rewrite ocd mem_cat cin.
have close_lc : close_alive_edges lc future_events.
  suff/head_not_end : close_alive_edges lc (e :: future_events).
    by apply=> c0 cin; apply: dec_not_end; rewrite cin orbT.
  apply/allP=> c0 cin; apply: (allP clae).
  by rewrite ocd !(mem_cat, inE) cin !orbT.
have endle : end_edge le future_events.
  suff  : end_edge le (e :: future_events).
    rewrite /end_edge; move=> /orP[-> // | ] /= /orP[ | ->]; last first.
      by rewrite orbT.
    by move: pal=> /[swap] /eqP <-; rewrite right_pt_below.
  have := (proj1 (andP (allP clae (head lcc cc) _))); rewrite leq; apply.
  by rewrite ocd; case : (cc) => [ | ? ?]; rewrite !(mem_cat, inE) eqxx ?orbT.
have endhe : end_edge he future_events.
  suff  : end_edge he (e :: future_events).
    rewrite /end_edge; move=> /orP[-> // | ] /= /orP[ | ->]; last first.
      by rewrite orbT.
    move: puh=> /[swap] /eqP <-; rewrite strict_nonAunder; last first.
      by apply: valid_edge_right.
    by rewrite right_on_edge.
  have := (proj2 (andP (allP clae lcc _))); rewrite ?heq; apply.
  by rewrite ocd; case : (cc) => [ | ? ?]; rewrite !(mem_cat, inE) eqxx ?orbT.
move: cle => /= /andP[] cloe _.
have clan := opening_cells_close vle vhe oute endle endhe cloe.
have main := (insert_opening_closeness close_fc clan close_lc).
split.
  by move: main; rewrite /opening_cells oca_eq -cats1 -!catA.
have subfc : {subset fc <= open} by move=> x xin; rewrite ocd mem_cat xin.
have sublc : {subset lc <= open}.
  by move=> x xin; rewrite ocd !(mem_cat, inE) xin !orbT.
have svaln : seq_valid ((fc ++ nos) ++ nlsto :: lc) p.
  apply/allP=> x; rewrite !(mem_cat, inE) -orbA => /orP[xf | ].
    have /andP [vlx vhx] := allP sval x (subfc _ xf).
    have := (allP main x); rewrite mem_cat xf => /(_ isT) /andP claex.
    by rewrite (val_between vlx) ?(val_between vhx); case: claex.
  rewrite orbA=> /orP[ | xl]; last first.
    have /andP [vlx vhx] := allP sval x (sublc _ xl).
    move: elexp;rewrite lexePt_eqVlt => /orP[/eqP <- | elexp'].
      by rewrite vlx vhx.
    have := (allP main x).
    rewrite 2!mem_cat xl !orbT => /(_ isT) /andP claex.
    by rewrite (val_between vlx) ?(val_between vhx); case: claex.
  move=> xin; have xin' : x \in opening_cells (point e) (outgoing e) le he.
    by rewrite /opening_cells oca_eq mem_rcons inE orbC.
  have [vlx vhx] := andP (allP (opening_valid oute vle vhe) _ xin').
  have [eelx eehx] := andP (allP clan _ xin').
  by rewrite (val_between vlx) ?(val_between vhx).
split.
  by exact: svaln.
have oute' :
     {in sort (@edge_below _) (outgoing e), forall g, left_pt g == (point e)}.
  by move=> x; rewrite mem_sort; apply: oute.
have [adjnew lownew] := adjacent_opening_aux' vle vhe oute' oca_eq.
have := opening_cells_aux_high_last vle vhe oute'; rewrite oca_eq heq /=.
move=> hnlsto.
split.
  suff : adjacent_cells ((fc ++ nos) ++ nlsto :: lc) by [].
  rewrite -catA.
  have oldnnil : rcons cc lcc != nil.
    by apply/eqP/rcons_neq0.
  rewrite -cat_rcons; apply: (replacing_seq_adjacent oldnnil).
  - by apply/eqP/rcons_neq0.
  - by apply/esym; rewrite lownew; move: leq; case: (cc) => [ | ? ?].
  - by rewrite !last_rcons.
  - by move: adj; rewrite ocd cat_rcons.
  by apply: adjnew.
have nn0 : rcons nos nlsto != nil by apply/eqP/rcons_neq0.
have on0 : rcons cc lcc != nil by apply/eqP/rcons_neq0.
move: cbtom; rewrite ocd -cat_rcons => cbtom'.
have hds: low (head dummy_cell (rcons cc lcc)) =
  low (head dummy_cell (rcons nos nlsto)).
  by rewrite head_rcons -leq -lownew head_rcons.
have tls : high (last dummy_cell (rcons cc lcc)) =
          high (last dummy_cell (rcons nos nlsto)).
  by rewrite !last_rcons.
split.
  move: cbtom'; 
  rewrite (replacing_seq_cells_bottom_top _ _ _ _ on0 nn0) //.
  by rewrite -catA cat_rcons.
rewrite -catA -cat_rcons.
have lein' : le \in all_edges open (e :: future_events) by rewrite mem_cat lein.
have hein' : he \in all_edges open (e :: future_events) by rewrite mem_cat hein.
have lebhe : le <| he.
  by apply: (edge_below_from_point_above (noc _ _) vle vhe (underWC _)).
have noc2 : {in [:: le, he & outgoing e] &, no_crossing R}.
  by move=> x y ; rewrite !inE=>/orP[/eqP -> | /orP[/eqP -> | xin]]
     /orP[/eqP -> | /orP[/eqP -> | yin]];
  try solve [left=> //; apply: edge_below_refl |
        apply: noc=> //; rewrite ?mem_cat ?yin ?xin ?orbT //].
have subso : {subset sort (@edge_below _) (outgoing e)
                <= all_edges open (e :: future_events)}.
  by move=> x; rewrite mem_sort; apply: subo.
apply/allP=> x; rewrite 2!mem_cat orbCA => /orP[xin | xold]; last first.
  move: rfo; rewrite ocd -cat_rcons=> /allP; apply.
  by rewrite 2!mem_cat orbCA xold orbT.
have srt : path (@edge_below _) le (sort (@edge_below _) (outgoing e)).
  by have := sorted_outgoing vle vhe pal puh oute noc2.
have := (opening_cells_aux_right_form (underWC pal) puh vle vhe
               lein' hein' lebhe oute' noc subso srt oca_eq).
by move=> /allP /(_ x xin).
Qed.

Let oute' : {in sort (@edge_below _) (outgoing e),
    forall g, left_pt g == (point e)}.
Proof. by move=> x; rewrite mem_sort; apply: oute. Qed.

Let vlo : valid_edge (low lsto) (point e).
Proof. by apply: (proj1 (andP (allP sval lsto lstoin))). Qed.

Let vho : valid_edge (high lsto) (point e).
Proof. by apply: (proj2 (andP (allP sval lsto lstoin))). Qed.

Lemma adjacent_update_open_cell new_op new_lsto:
  update_open_cell lsto e = (new_op, new_lsto) ->
  low lsto = low (head dummy_cell (rcons new_op new_lsto)) /\
  high lsto = high (last dummy_cell (rcons new_op new_lsto)) /\
  adjacent_cells (rcons new_op new_lsto).
Proof.
rewrite /update_open_cell.
case o_eq : (outgoing e) => [ | g os].
  by move=> [] <- <- /=.
rewrite -o_eq.
move=> oca_eq.
have [-> ->] := adjacent_opening_aux' vlo vho oute' oca_eq.
have := opening_cells_aux_high_last vlo vho oute'.
by rewrite oca_eq last_rcons /= => ->.
Qed.

Let loin : low lsto \in all_edges open (e :: future_events).
Proof. by rewrite 2!mem_cat map_f. Qed.

Let hoin : high lsto \in all_edges open (e :: future_events).
Proof. by rewrite 2!mem_cat map_f // orbT. Qed.

Lemma update_open_cell_right_form  new_op new_lsto:
  update_open_cell lsto e = (new_op, new_lsto) ->
  point e <<< high lsto ->
  point e >>> low lsto ->
  s_right_form (rcons new_op new_lsto).
Proof.
move=> + puho palo.
have noco : below_alt (low lsto) (high lsto).
  by apply: noc; rewrite 2!mem_cat map_f ?orbT.
have rflsto : low lsto <| high lsto.
  by apply: (edge_below_from_point_above noco vlo vho (underWC _)).
rewrite /update_open_cell.
case ogeq : (outgoing e) => [ | g os].
  move=> [] <- <- /=; rewrite andbT.
  by apply: (edge_below_from_point_above noco vlo vho (underWC _)).
move=> oca_eq.
rewrite -ogeq in oca_eq.
have srt : path (@edge_below _) (low lsto) (sort (@edge_below _) (outgoing e)).
  apply: (sorted_outgoing vlo vho palo puho oute).
  apply: sub_in2 noc=> x; rewrite 2!inE => /orP[/eqP ->  | /orP[/eqP -> | ]] //.
  by apply: subo.
have := opening_cells_aux_right_form (underWC palo)
  puho vlo vho loin hoin rflsto oute' noc subo' srt oca_eq.
by [].
Qed.

Lemma step_keeps_invariant1 :
  invariant1 (step e (Bscan fop lsto lop cls lstc lsthe lstx)).
Proof.
rewrite /invariant1.
case step_eq : (step _ _) => [fop' lsto' lop' cls' lstc' lsthe' lstx']. 
rewrite /state_open_seq /=; move: step_eq.
rewrite /step -/open.
have val_bet := valid_between_events elexp plexfut _ inbox_p.
case: ifP=> [pxaway | /negbFE/eqP/[dup] pxhere /abovelstle palstol].
  move: default_case.
  case oe: (open_cells_decomposition _ _) => [[[[[fc cc ] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno] def_case.
  rewrite /invariant1/state_open_seq /= in def_case.  
  move=> [] <- <- <- _ _ _ _.
  apply: (def_case [::] lno (high lno)) (p_x (point e)).
have infop : {subset fop <= open}.
  by move=> x xin; rewrite /open mem_cat xin.
have sval1 : seq_valid fop (point e).
  by apply/allP=> x xin; apply: (allP sval); apply: infop.
have rfo1 : s_right_form fop.
  by apply/allP=> x xin; apply: (allP rfo); apply: infop.
have adj1 : adjacent_cells fop.
  by move: adj; rewrite /open => /adjacent_catW[].
have allnct1 : {in fop, forall c, ~contains_point (point e) c}.
  case fop_eq : fop => [// | c1 fop1].
  have := above_all_cells sval1 adj1 rfo1.
  have hfopq : high (last dummy_cell fop) = low lsto.
    by move: adj; rewrite /open fop_eq /= cat_path => /andP[] _ /= /andP[] /eqP.
  move: palstol; rewrite hfopq=> -> /(_ isT) [] _ M.
  by rewrite -fop_eq=> x xin; rewrite /contains_point (negbTE (M x xin)) andbF.
have inlop : {subset lop <= open}.
  by move=> x xin; rewrite !(mem_cat, inE) xin !orbT.
have lopclae : close_alive_edges lop (e :: future_events).
  by apply/allP=> x xin; apply: (allP clae x); apply inlop.
have fop_note x : x \in fop ->
  ~ event_close_edge (low x) e /\ ~ event_close_edge (high x) e.
  move=> xin; apply: contrapositive_close_imp_cont.
  - by apply: (allP rfo); rewrite /open mem_cat xin.
  - by apply/andP; apply: (allP sval); rewrite /open mem_cat xin.
  by apply: allnct1.
have fopclae : close_alive_edges fop (e :: future_events).
  by apply/allP=> x xin; apply: (allP clae); rewrite mem_cat xin.
move: (cle) => /= /andP[] cloe _.
case: ifP=> [eabove | ebelow].
  case oe: (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      by move: adj=> /adjacent_catW[] _; case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  move=> [] <- <- <- _ _ _ _.
  have := default_case nil lsto lsthe (p_x (point e)).
  by rewrite oe' oca_eq /invariant1 /state_open_seq /= cat_rcons.
have [vllsto vhlsto] : valid_edge (low lsto) (point e) /\
                       valid_edge (high lsto) (point e).
  move: sval=> /allP /(_ lsto); rewrite /open mem_cat inE eqxx orbT.
  by move=> /(_ isT) /andP.
case: ifP => [ebelow_st | eonlsthe].
  have vlop : seq_valid lop (point e).
    by apply/allP=> x xin; apply: (allP sval); apply: inlop.
  have rlop : s_right_form lop.
    by apply/allP=> x xin; apply: (allP rfo); apply: inlop.
  have alop : adjacent_cells lop.
    by move: adj; rewrite /open -cat_rcons=> /adjacent_catW[].
  have strulop x (xin: x \in lop) : point e <<< high x.
    case lop_eq : lop xin => [ // | c {}lop']; rewrite -lop_eq=> xin.
    have := below_all_cells vlop alop rlop.
    suff -> : low (head dummy_cell lop) = lsthe.
      by rewrite ebelow_st => /(_ isT x xin).
    move: adj=> /adjacent_catW[] _.
    by rewrite lop_eq lstheq /= =>/andP[] /eqP <-.
  have lop_note x (xin : x \in lop) :
    ~ event_close_edge (low x) e /\ ~ event_close_edge (high x) e.
    have blx : point e <<< low x.
      move: xin=> /mem_seq_split [s1 [s2 lop_eq]].
      elim/last_ind: {-1}(s1) (erefl s1) => [ | s1' x0 _] s1_eq.
        move: adj; rewrite /open lop_eq s1_eq /= => /adjacent_catW[] _.
        by rewrite /= => /andP[] /eqP <-; rewrite -lstheq.
      move: adj; rewrite /open lop_eq s1_eq /= => /adjacent_catW[] _.
      rewrite /= cat_path last_rcons /= => /andP[] _ /andP[] /eqP <- _.
      by apply: strulop; rewrite lop_eq s1_eq !(mem_cat, mem_rcons, inE) eqxx.
    have nlo : ~ event_close_edge (low x) e.
      move: blx => /[swap] /eqP <-.
      by rewrite -(negbK (_ <<< _)) right_pt_above.
    have nhi // : ~ event_close_edge (high x) e.
    move: (strulop _ xin) => /[swap] /eqP <-.
    by rewrite -(negbK (_ <<< _)) right_pt_above.
  case uoc_eq : (update_open_cell _ _) =>
    [new_op new_lsto] [] <- <- <- _ _ _ _.
  have clae_part : close_alive_edges ((fop ++ new_op) ++ new_lsto :: lop)
           future_events.
    apply/allP=> x; rewrite !(mem_cat, inE) -!orbA.
    move=> /orP[xinf | ].
      by apply: (allP (head_not_end fopclae fop_note)).
    have [vlstl vlsth] : valid_edge (low lsto) (point e) /\
        valid_edge (high lsto) (point e).
      by apply/andP/(allP sval); rewrite mem_cat inE eqxx orbT.
    have lowlsto_not_end : ~~event_close_edge (low lsto) e.
      by apply/negP=> /eqP abs; move: palstol; rewrite -abs right_pt_below.
    have highlsto_not_end : ~~event_close_edge (high lsto) e.
      apply/negP=>/eqP abs.
      by move: ebelow_st; rewrite lstheq -abs -(negbK(_ <<< _)) right_pt_above.
    have lowlsto_end : end_edge (low lsto) future_events.
      have := (proj1 (andP (allP clae lsto lstoin))); rewrite /end_edge /=.
      by rewrite (negbTE lowlsto_not_end).
    have highlsto_end : end_edge (high lsto) future_events.
      have := (proj2 (andP (allP clae lsto lstoin))); rewrite /end_edge /=.
      by rewrite (negbTE highlsto_not_end).
    move=> /orP[ xin |].
      move: uoc_eq; rewrite /update_open_cell.
      case out_eq : (outgoing e) => [ | g outs].
        by move: xin=> /[swap] -[] <- _ //=.
      rewrite -out_eq=> oca_eq.
      have := opening_cells_close vlstl vlsth oute lowlsto_end highlsto_end cloe.
      move/allP=> /(_ x); rewrite /opening_cells oca_eq mem_rcons inE xin orbT.
      by apply.
    move=> /orP[ /eqP -> | ].
      move: uoc_eq; rewrite /update_open_cell.
      case out_eq : (outgoing e) => [ | g outs].
        by move=> -[] _ <- /=; rewrite lowlsto_end highlsto_end.
      rewrite -out_eq=> oca_eq.
      have := opening_cells_close vlstl vlsth oute lowlsto_end highlsto_end cloe.
      move/allP=>/(_ new_lsto); rewrite /opening_cells oca_eq mem_rcons inE eqxx.
      by apply.
    by move=> xin; apply: (allP (head_not_end lopclae _) x xin).
  split=> //.
  rewrite -cat_rcons -cats1 -(catA _ _ [:: new_lsto]) cats1.
  split.
    apply/allP=> x; rewrite 2!mem_cat (orbC (_ \in fop)) -orbA=> /orP[] xin.
      have /andP[eelx eehx] : end_edge (low x) future_events &&
                          end_edge (high x) future_events.
        apply: (allP clae_part); rewrite -cat_rcons -cats1 -(catA fop).
        by rewrite cats1 2!mem_cat xin orbT.
      have [vlxe vhxe] : valid_cell x (point e).
        move: uoc_eq; rewrite /update_open_cell.
        case o_eq : (outgoing e) xin => [ | g s].
          by move=> /[swap] -[] <- <-; rewrite /valid_cell inE=> /eqP ->.
        move=> xin.
        have := allP (opening_valid oute vlo vho).
        rewrite /opening_cells=>/[swap].
        rewrite -o_eq; case: (opening_cells_aux _ _ _ _) =>
           a b [] -> -> /(_ _ xin).
        by move/andP.
      by rewrite !val_bet.
    have /andP[vlx vhx] :
    valid_edge (low x) (point e) && valid_edge (high x) (point e).
      apply: (allP sval); rewrite /open !(mem_cat, inE).
      by move: xin=> /orP[] ->; rewrite ?orbT.
    have /andP[eex eehx] :
     end_edge (low x) future_events && end_edge (high x) future_events.
      apply: (allP clae_part x); rewrite !(mem_cat, inE).
      by move: xin=> /orP[] ->; rewrite ?orbT.
    by rewrite !val_bet.
  rewrite -catA.
  have lstonnil : [:: lsto] != nil by [].
  have [lq [hq adjnew]] := adjacent_update_open_cell uoc_eq.
  split.
    apply: (replacing_seq_adjacent lstonnil).
    - by apply/eqP/rcons_neq0.
    - by rewrite /= lq.
    - by rewrite /= hq.
    - by rewrite /= adj.
    by apply: adjnew.
  split.
    rewrite -(replacing_seq_cells_bottom_top _ _ _ _ lstonnil) //.
    by apply/eqP/rcons_neq0.
  rewrite /s_right_form all_cat; apply/andP; split.
    by apply/allP=> x xin; apply: (allP rfo); rewrite mem_cat xin.
  rewrite all_cat; apply/andP; split; last first.
    by apply/allP=> x xin; apply: (allP rfo); rewrite mem_cat inE xin ?orbT.
  apply: update_open_cell_right_form => //.
  by move: ebelow_st; rewrite lstheq.
have lsto_ctn : contains_point'(point e) lsto.
  by rewrite /contains_point' -lstheq (negbFE ebelow) abovelstle.
have exi2 : exists2 c, c \in (lsto :: lop) & contains_point' (point e) c.
  by exists lsto; rewrite // inE eqxx.
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
  rewrite oe => oe'.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
  open_cells_decomposition_main_properties oe' exi.
have [ocd' _] := open_cells_decomposition_main_properties oe exi2.
have fc'0 : fc' = [::].
  case fc_eq : (fc') => [ // | a fc2].
  rewrite fc_eq /= in ocd'; move: ocd'=> [] lstoa; rewrite -lstoa in fc_eq.
  move: (all_nct lsto); rewrite mem_cat fc_eq inE eqxx orbT=> /(_ isT).
  by rewrite (contains_point'W lsto_ctn).
rewrite /update_open_cell_top.
case o_eq : (outgoing e) => [ | g l]; rewrite -?o_eq; last first.
  have := (default_case [::] dummy_cell dummy_edge 0); rewrite oe'.
  have llstoq : low lsto = le.
    move: ocd => /eqP; rewrite fc'0 cats0 eqseq_cat // eqxx /= leq => /eqP.
    by case: (cc) => [ | ? ?] -[] ->.
  rewrite llstoq.
  case: (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /invariant1 /state_open_seq /= => inv1 [] <- <- <- _ _ _ _.
  by rewrite !catA.
move=> [] <- <- <- _ _ _ _ /=.
have subf : {subset (fop ++ fc') <= open}.
  by move=> x xin; rewrite /open ocd mem_cat xin.
have adjf : adjacent_cells (fop ++ fc').
  by move: adj; rewrite /open ocd=> /adjacent_catW[].
have claef : close_alive_edges (fop ++ fc') (e :: future_events).
  by apply/allP=> x xin; apply: (allP clae); apply: subf.
have rfof : s_right_form (fop ++ fc').
  by apply/allP=> x xin; apply: (allP rfo); apply: subf.
have svalf : seq_valid (fop ++ fc') (point e).
  by apply/allP=> x xin; apply: (allP sval); apply: subf.
have subl : {subset (lsto :: lop) <= open}.
  by move=> x xin; rewrite /open mem_cat xin orbT.
have adjl : adjacent_cells (lsto :: lop).
  by move: adj=> /adjacent_catW[].
have rfol : s_right_form (lsto :: lop).
  by apply/allP=> x xin; apply: (allP rfo); apply: subl.
have svall : seq_valid (lsto :: lop) (point e).
  by apply/allP=> x xin; apply: (allP sval); apply: subl.
have cbtom' : cells.cells_bottom_top (low lsto) top (lsto :: lop).
  move: cbtom; rewrite /open /cells.cells_bottom_top /cells_low_e_top eqxx //=.
  by move=> /andP[] _; rewrite last_cat /=.
have bet : between_edges (low lsto) top (point e).
  rewrite /between_edges (proj1 (andP lsto_ctn)).
  by move: inbox_e=>/andP[]/andP[] _ -> _.
have [pal puh vl vh not_ct] := 
  connect_properties cbtom adj rfo sval (inside_box_between inbox_e)
     ocd all_nct all_ct lcc_ctn flcnct.
have claef' : close_alive_edges (fop ++ fc') future_events.
  elim/last_ind: {-1}(fop ++ fc') (erefl (fop ++ fc')) => [// | fc2 c2 _] f_eq.
  have hc2q : high c2 = low (head lcc cc).
    move: adj; rewrite /open ocd catA f_eq -cats1 -!catA=> /adjacent_catW[] _.
    by rewrite /=; case: (cc) => [ | ? ?] /andP[] /eqP.
  have palst : point e >>> high (last dummy_cell (fop ++ fc')).
    by rewrite f_eq last_rcons hc2q.
  have [above_l above_h] := above_all_cells svalf adjf rfof palst.
  have {}allabove_l : {in fop ++ fc', forall c, point e >>> low c}.
    move=> c /mem_seq_split [s1 [s2 s_q]].
      elim/last_ind : {-1} (s1) (erefl s1) => [ | s1' c1 _] s1q.
        by move: above_l; rewrite s_q s1q /=.
      have : point e >>> high c1.
        by rewrite above_h // s_q s1q mem_cat mem_rcons inE eqxx.
      have /eqP -> // : high c1 == low c.
      move: adjf; rewrite s_q s1q -cats1 -catA /= => /adjacent_catW[] _.
      by rewrite /= => /andP[].
  have f_not_end : forall c, c \in fop ++ fc' ->
  ~ event_close_edge (low c) e /\ ~ event_close_edge (high c) e.
    move=> c cin; apply: contrapositive_close_imp_cont.
    - by apply: (allP rfof).
    - by apply/andP; apply: (allP svalf).
    by apply/negP; rewrite /contains_point (negbTE (above_h _ cin)) andbF.
  apply/allP=> x; rewrite -f_eq => xin.
  by apply: (allP (head_not_end claef f_not_end)).  
have clael : close_alive_edges lc (e :: future_events).
  apply/allP=> x xin.
  by apply: (allP clae); rewrite /open ocd !mem_cat inE xin !orbT.
have clael' : close_alive_edges lc future_events.
  case lc_eq : (lc) => [ // | c2 lc2]; rewrite -lc_eq.
  have [puhlcc adj2] : point e <<< low (head dummy_cell lc) /\
                        adjacent_cells lc.
    move: adj; rewrite /open ocd lc_eq.
    move=> /adjacent_catW[] _ /adjacent_catW[] _ /=.
    by move=> /andP[] /eqP <- ->.
  have sub2 : {subset lc <= open}.
    by move=> x xin; rewrite /open ocd !(mem_cat, inE) xin !orbT.
  have sval2 : seq_valid lc (point e).
    by apply/allP=> x xin; apply: (allP sval); apply: sub2.
  have rfo2 : s_right_form lc.
    by apply/allP=> x xin; apply: (allP rfo); apply: sub2.
  have below_h : {in lc, forall c, point e <<< high c}.
    exact: (below_all_cells sval2 adj2 rfo2 puhlcc).
  have below_l : {in lc, forall c, point e <<< low c}.
    move=> c /mem_seq_split [s1 [s2 s_q]].
    elim/last_ind : {2}(s1) (erefl s1) => [ | s1' c1 _] s1_q.
      by move: puhlcc; rewrite s_q s1_q /=.
    move: adj2; rewrite s_q s1_q -cats1 -catA=> /adjacent_catW [] _ /=.
    move=> /andP[]/eqP <- _; apply: below_h; rewrite s_q s1_q mem_cat.
    by rewrite mem_rcons inE eqxx.
  have l_not_end : forall c, c \in lc ->
  ~ event_close_edge (low c) e /\ ~ event_close_edge (high c) e.
    move=> c cin; apply: contrapositive_close_imp_cont.
    - by apply: (allP rfo2).
    - by apply/andP; apply: (allP sval2).
    by apply/negP; rewrite /contains_point negb_and negbK (below_l _ cin).
  apply/allP=> x xin.
  by apply: (allP (head_not_end clael l_not_end)).
rewrite cats0; set open' := (X in is_true (_ X _) /\ _); rewrite -/open'.
have clae_part : close_alive_edges open' future_events.
  rewrite /close_alive_edges all_cat [all _ (fop ++ fc')]claef' /=.
  rewrite [all _ lc]clael' andbT.
  have llsto_end : end_edge (low lsto) future_events.
    elim/last_ind : {-1} (fop ++ fc') (erefl (fop ++ fc')) => [ | fs c1 _] f_eq.
      move: f_eq; case fop_eq: (fop) => [ | //].
      move: cbtom; rewrite /open fop_eq /= => /andP[] /andP[] _ /= /eqP + _.
      by rewrite /end_edge !inE => -> _; rewrite eqxx.
    have <- : high c1 = low lsto.
      rewrite fc'0 cats0 in f_eq.
      move: adj; rewrite /open f_eq -cats1 -catA=>/adjacent_catW[] _ /=.
      by move=> /andP[] /eqP.
    apply: (proj2 (andP (allP claef' c1 _))).
    by rewrite f_eq mem_rcons inE eqxx.
  have he_end : end_edge he future_events.
    case lc_eq : lc => [ | c1 lc'].
      have hetop : he = top.
        move: cbtom=> /andP[] /andP[] _ _.
        by rewrite /open ocd lc_eq !last_cat -heq /= => /eqP.
      by rewrite /end_edge hetop !inE eqxx ?orbT.
    have hlccq : high lcc = low c1.
      move: adj; rewrite /open ocd lc_eq.
      by move=> /adjacent_catW[] _ /adjacent_catW[] _ /andP[] /eqP.
    have c1in : c1 \in lc by rewrite lc_eq inE eqxx.
    by have := (allP clael' _ c1in) => /andP[] + _; rewrite -hlccq -heq.
  by rewrite llsto_end he_end.
split=> //.
rewrite /seq_valid all_cat /= all_cat andbCA.
have vhe : valid_edge he (point e).
  rewrite heq; apply: (proj2 (andP (allP sval lcc _))).
  by rewrite /open ocd !mem_cat inE eqxx ?orbT.
split.
  apply/andP; split; last first.
    rewrite -!all_cat; apply/allP=> x xin.
    have /andP[vlx vhx] :
    valid_edge (low x) (point e) && valid_edge (high x) (point e).
      apply: (allP sval); rewrite /open ocd mem_cat [X in _ || X]mem_cat inE.
      by move: xin; rewrite mem_cat => /orP[] ->; rewrite ?orbT.
    have /andP[eelx eehx] :
     end_edge (low x) future_events && end_edge (high x) future_events.
      apply: (allP clae_part). 
      rewrite /open' mem_cat inE.
      by rewrite orbCA -mem_cat xin orbT.
    by rewrite !val_between.
  have eelo : end_edge (low lsto) future_events.
    have : end_edge (low lsto) (e :: future_events).
      by apply: (proj1 (andP (allP clae lsto _))).
    rewrite /end_edge /= => /orP[-> // | /orP[abs | ->]]; last by rewrite !orbT.
    by move: palstol; rewrite -(eqP abs) right_pt_below.
  have eehe : end_edge he future_events.
    have : end_edge (high lcc) (e :: future_events).
      apply: (proj2 (andP (allP clae lcc _))).
        by rewrite /open ocd !mem_cat inE eqxx !orbT.
      rewrite /end_edge heq /= => /orP[-> // | /orP[abs | ->]]; last first.
      by rewrite orbT.
    by move: puh; rewrite -(eqP abs) -[_ <<< _]negbK right_pt_above.
  by rewrite !val_between.
split.
  case feq : fop => [ | c0 f].
    rewrite /open' feq fc'0 /=.
    move: adj; rewrite /open ocd => /adjacent_catW[] _ /adjacent_catW[] _ /=.
    by case: (lc)=> [ // | c2 lc'] /=; rewrite heq.
  rewrite /open' -adjacent_cut /=; last by rewrite feq.
  apply/andP; split.
    apply/andP; split; last by move: adj; rewrite /open ocd=> /adjacent_catW.
    rewrite fc'0 cats0; move: adj; rewrite /open feq /= cat_path /=.
    by move=> /andP[] _ /andP[].
  move: adj; rewrite /open ocd => /adjacent_catW[] _ /adjacent_catW[] _ /=.
  by case: (lc) => [// | c2 l'] /=; rewrite heq.
have on0 : rcons cc lcc != nil by apply/eqP/rcons_neq0.
rewrite /open'.
set nc := Bcell _ _ _ _.
have nn0 : [:: nc] != nil by [].
split.
  rewrite -(replacing_seq_cells_bottom_top _ _ _ _ on0 nn0).
  - by rewrite cat_rcons -ocd.
  - rewrite /nc /= head_rcons.
    move: ocd'; rewrite fc'0 /=.
    by case: (cc) => [ //= | c1 ?] /= [] ->.
  by rewrite /nc/= last_rcons.
rewrite /s_right_form all_cat /=; apply/andP; split.
  by apply/allP=> x xin; apply: (allP rfo); rewrite /open ocd mem_cat xin.
apply/andP; split; last first.
  apply/allP=> x xin; apply: (allP rfo).
  by rewrite /open ocd !(mem_cat, inE) xin ?orbT.
have noclstohe : below_alt he (low lsto).
  apply: noc=> //.
  by rewrite mem_cat hein.
have puh' : point e <<< he by rewrite heq.
have := edge_below_from_point_under noclstohe vhe vlo (underW puh') palstol.
by [].
Qed.

Hypothesis btom_left_corners :
  {in open, forall c, lexPt (bottom_left_corner c) (point e)}.  

Lemma lex_left_pts_inf' :
  let '(fc, _, _, lc, le, he) :=
    open_cells_decomposition open (point e) in
  let '(nos, lno) :=
    opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he in
    {in fc ++ nos ++ lno :: lc,
      forall c, lexePt  (bottom_left_corner c) (point e)}.
Proof.
case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
have [ocd [_ [_ [_ [_ [leq [heq [lein hein]]]]]]]]:=
  open_cells_decomposition_main_properties oe exi.
have [pal puh vle vhe A']:= decomposition_connect_properties rfo sval adj cbtom
  (inside_box_between inbox_e) oe.
have sublehe : {subset rcons (le :: sort (@edge_below _) (outgoing e)) he <=
                  all_edges open (e :: future_events)}.
  move=> x; rewrite mem_rcons inE => /orP[/eqP -> | ].
    by rewrite mem_cat hein.
  rewrite inE=> /orP[/eqP -> | ].
    by rewrite mem_cat lein.
  by apply: subo'.
have noc2:
   {in rcons (le :: sort (@edge_below _) (outgoing e)) he &, no_crossing R}.
  by move=> x y xin yin; apply: noc; apply: sublehe.
move=> x; rewrite !(mem_cat, inE) => /orP[xfc | ].
  by apply: lexPtW; apply: btom_left_corners;rewrite ocd mem_cat xfc.
rewrite orbA=> /orP[xin | xlc]; last first.
  apply: lexPtW.
  by apply: btom_left_corners; rewrite ocd !(mem_cat, inE) xlc !orbT.
have noclh : below_alt le he.
  by apply: noc2; rewrite ?(mem_rcons, inE) eqxx ?orbT.
have lebhe : le <| he.
  apply: (edge_below_from_point_above noclh vle vhe (underWC pal) puh).
have := opening_cells_last_lexePt oute (underWC pal) puh vle vhe noc2 lebhe.
rewrite /opening_cells oca_eq; apply.
by rewrite mem_rcons inE orbC.
Qed.

Lemma lex_left_pts_inf q :
  lexPt (point e) q ->
  let '(fc, _, _, lc, le, he) :=
    open_cells_decomposition open (point e) in
  let '(nos, lno) :=
    opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he in
    {in fc ++ nos ++ lno :: lc, forall c, lexPt  (bottom_left_corner c) q}.
Proof.
move=> lexq.  
case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
case oca_eq: (opening_cells_aux _ _ _ _) => [nos lno].
have := lex_left_pts_inf'; rewrite oe oca_eq => main.
by move=> x xin; apply: lexePt_lexPt_trans lexq; apply: main.
Qed.

Lemma leftmost_points_max :
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  left_limit (start_open_cell bottom top) =
  max (p_x (left_pt bottom)) (p_x (left_pt top)).
Proof.
rewrite /start_open_cell /leftmost_points => /andP[] /=.
case: ltrP => cmpl.
  case peq: (vertical_intersection_point (left_pt top) bottom) => [p' | //].
  move=> _ /andP[] samex _ /=.
  move: peq; rewrite /vertical_intersection_point.
  by case: ifP=> // ve [] <-.
case peq: (vertical_intersection_point (left_pt bottom) top)=> [p' | //].
by move=> _ /andP[].
Qed.

Lemma close_cell_ok c :
  contains_point (point e) c ->
  valid_edge (low c) (point e) -> valid_edge (high c) (point e) ->
  open_cell_side_limit_ok c ->
  closed_cell_side_limit_ok (close_cell (point e) c).
Proof.
move=> ctp vl vh.
rewrite /open_cell_side_limit_ok/closed_cell_side_limit_ok.
rewrite /close_cell /=; have /exists_point_valid [p1 /[dup] vip1 ->] := vl.
have /exists_point_valid [p2 /[dup] vip2 -> /=] := vh.
move=> /andP[] -> /andP[]-> /andP[]-> /andP[] -> -> /=.
have [o1 x1]:=intersection_on_edge vip1; have [o2 x2]:=intersection_on_edge vip2.
rewrite -?(eq_sym (point e)).
case:ifP=>[/eqP q1 | enp1];case:ifP=>[/eqP q2 | enp2]; move: (o1) (o2);
 rewrite /=  -?q1 -?q2 -?x1 -?x2 ?eqxx/= => -> ->; rewrite ?andbT //=.
- move: ctp=> /andP[] _ eh.
  by apply: (under_edge_strict_lower_y x2 (negbT enp2) eh).
- move: ctp=> /andP[] el _.
  by apply: (above_edge_strict_higher_y x1 (negbT enp1) el).
move: ctp=> /andP[] el eh.
by rewrite (above_edge_strict_higher_y x1 (negbT enp1) el) //
      (under_edge_strict_lower_y x2 (negbT enp2) eh).
Qed.

Lemma closing_cells_side_limit' cc :
  s_right_form cc ->
  seq_valid cc (point e) ->
  adjacent_cells cc ->
  all open_cell_side_limit_ok cc ->
  all (contains_point (point e)) cc ->
  point e >>> low (head dummy_cell cc) ->
  point e <<< high (last dummy_cell cc) ->
  all (@closed_cell_side_limit_ok _) (closing_cells (point e) cc).
Proof.
move=> rfc valc adjc oks ctps abovelow belowhigh.
rewrite /closing_cells.
rewrite all_map.
apply/allP=> //= c cin.
have vlc : valid_edge (low c) (point e) by have := (allP valc c cin) => /andP[].
have vhc : valid_edge (high c) (point e)
   by have := (allP valc c cin) => /andP[].
apply: close_cell_ok=> //.
  by apply: (allP ctps).
by apply: (allP oks).
Qed.

Lemma close'_subset_contact q c :
  valid_cell c (point e) ->
  closed_cell_side_limit_ok (close_cell (point e) c) ->
  inside_closed' q (close_cell (point e) c) -> inside_open' q c.
Proof.
move=>[] vl vh.
move=>/closed_right_imp_open.
rewrite inside_open'E // inside_closed'E /close_cell.
have [p1 vip1] := exists_point_valid vl.
have [p2 vip2] := exists_point_valid vh.
rewrite vip1 vip2 /= => cok /andP[] -> /andP[] -> /andP[] -> rlim /=.
by apply: (le_trans rlim cok).
Qed.

Lemma close_cell_right_limit c :
  valid_cell c (point e) ->
  right_limit (close_cell (point e) c) = p_x (point e).
Proof.
move=> [vl vh].
rewrite /close_cell; rewrite !pvertE // /right_limit /=.
by case: ifP=> cnd1 //; case: ifP=> cnd2.
Qed.

Lemma in_new_cell_not_in_first_old fc cc lcc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  all open_cell_side_limit_ok open ->
  {in [seq high c | c <- fc], forall g, p_x (point e) < p_x (right_pt g)} ->
  {in fc & opening_cells (point e) (outgoing e) le he,
     forall c1 c2, o_disjoint c1 c2}.
Proof.
move=> oe lok redges.
have [ocd [_ [_ [_ [_ [heq [leq [lein hein]]]]]]]] :=
   open_cells_decomposition_main_properties oe exi.
have [pal puh vle vhe X] :=
  decomposition_connect_properties rfo sval adj cbtom 
    (inside_box_between inbox_e) oe.
set result_open :=
   fc ++ opening_cells (point e) (outgoing e) le he ++ lc.
rewrite /opening_cells.
case oca_eq : (opening_cells_aux _ _ _ _) => [s' c'].
have adj' : adjacent_cells result_open.
  rewrite /result_open /opening_cells oca_eq.
  have oldnnil : rcons cc lcc != nil by case: (cc).
  have newnnil : rcons s' c' != nil by case: (s').
  apply: (replacing_seq_adjacent oldnnil newnnil).
  - have := lower_edge_new_cells vle vhe.
    rewrite /opening_cells oca_eq=> /(_ _ erefl) /eqP ->.
    by rewrite head_rcons -leq.
  - have := higher_edge_new_cells oute vle vhe.
    rewrite /opening_cells oca_eq => /(_ _ erefl) /eqP ->.
    by rewrite last_rcons heq.
  - by rewrite -cats1 -!catA -ocd.
  by have := adjacent_opening' vle vhe oute; rewrite /opening_cells oca_eq.
have nceq : opening_cells (point e) (outgoing e) le he = rcons s' c'.
  by rewrite /opening_cells oca_eq.
have [nle nhe]:=
    higher_lower_equality oute oe nceq (exists_cell cbtom adj 
         (inside_box_between inbox_e))
         vle vhe.
have [fceq | [fc' [lfc fceq]]] : fc = nil \/ exists fc' lfc, fc = rcons fc' lfc.
    by elim/last_ind : (fc) => [ | fc' lfc _];[left | right; exists fc', lfc].
  by rewrite fceq.
have lfceq : high lfc = le.
  have := last_first_cells_high cbtom adj 
             (inside_box_between inbox_e) oe; rewrite fceq.
  by rewrite map_rcons last_rcons.
set s1 := [seq high c | c <- fc'].
set s2 := [seq high c | c <- behead (rcons s' c') ++ lc].
set g2 := high (head dummy_cell (rcons s' c')).
have roeq : [seq high c | c <- result_open] = s1 ++ [:: le, g2 & s2].
  rewrite /result_open nceq map_cat fceq -cats1 map_cat -catA /=.
  congr (_ ++ (_ :: _)) => //.
  rewrite /g2 /s2 2!map_cat.
  by case: (s').
have headin : head dummy_cell (rcons s' c') \in rcons s' c'.
  by rewrite headI inE eqxx.
have val' : all (fun g => @valid_edge R g (point e)) (s1 ++ [:: le, g2 & s2]).
  apply/allP=> g; rewrite mem_cat=> /orP[/mapP[c cin ->] | innc].
    apply/(seq_valid_high sval)/map_f; rewrite ocd fceq mem_cat mem_rcons.
    by rewrite inE cin orbT.
  move: innc; rewrite inE=> /orP[/eqP -> // | gnew].
    have [c cin ->] : exists2 c, c \in rcons s' c' ++ lc & g = high c.
      move: gnew; rewrite inE => /orP[gg2 | gs2].
      exists (head dummy_cell (rcons s' c'));[ | by rewrite (eqP gg2)].
      by rewrite mem_cat headin.
    move: gs2; rewrite /s2 map_cat mem_cat => /orP[].
      move=> /mapP[c /behead_subset cin ->]; exists c=> //.
      by rewrite mem_cat cin.
    by move=> /mapP[c cin ->]; exists c=> //; rewrite mem_cat cin orbT.
  move: cin; rewrite mem_cat=> /orP[] cin; last first.
    by apply/(seq_valid_high sval)/map_f; rewrite ocd !(mem_cat, inE) cin !orbT.
  have := opening_cells_subset vle vhe oute => /(_ c).
  rewrite nceq => /(_ cin)=> /andP[] _.
  rewrite /= inE => /orP[/eqP -> //| /oute it].
  by apply: valid_edge_extremities; rewrite it.
have noco : {in cell_edges open &, no_crossing R}.
  by apply: (sub_in2 _ noc)=> x xin; rewrite mem_cat xin.
have headccin : head lcc cc \in open.
  by rewrite ocd !mem_cat; case: (cc) => [ | ? ?] /=; rewrite !inE eqxx ?orbT.
have lein' : le \in all_edges open (e :: future_events).
  by rewrite mem_cat lein.
have hein' : he \in all_edges open (e :: future_events).
  by rewrite mem_cat hein.
have  [edgesabove edgesbelow noce]:=
   outgoing_conditions pal puh lein' hein' vle vhe subo noc oute.
have lbh : le <| he.
  by apply: (open_cells_decomposition_low_under_high noco cbtom _
              (inside_box_between _) _ _ oe).
have rfr' : sorted (@edge_below R) (s1 ++ [:: le, g2 & s2]).
  have rfnew : s_right_form (opening_cells (point e) (outgoing e) le he).
      by apply: (opening_cells_right_form vle vhe (underWC pal) _ _ _ _ _ noce).
  have rfr : s_right_form result_open.
    apply/allP=> x; rewrite /result_open !mem_cat orbCA => /orP[ | /orP xold ].
      by apply: (allP rfnew).
    by apply: (allP rfo); rewrite ocd !(mem_cat, inE); move: xold=>[] ->;
       rewrite ?orbT.
  have := seq_edge_below' adj' rfr; rewrite roeq.
  by have /path_sorted := seq_edge_below' adj' rfr; rewrite roeq.
set p' := Bpt (p_x (point e)) (pvert_y (point e) le).
have samex : p_x (point e) == p_x p' by apply: eqxx.
have vle' : valid_edge le p' by rewrite -(same_x_valid le samex).
have vg2 : valid_edge g2 (point e).
  by apply: (allP val'); rewrite !mem_cat !inE; rewrite eqxx !orbT.
have vg2' : valid_edge g2 p'.
   by rewrite -(same_x_valid _ samex).
have p'above : p' >>= le.
  by rewrite (strict_nonAunder vle') negb_and negbK (pvert_on vle).
have p'under : p' <<< g2.
  have := opening_cells_subset vle vhe oute; rewrite nceq => /(_ _ headin).
  move=> /andP[] _; rewrite -/g2 => g2in.
  rewrite (strict_under_pvert_y vg2').
  rewrite -(eqP (same_pvert_y vg2 samex)).
  apply: (lt_le_trans (_ : p_y p' < p_y (point e))).
    by rewrite [X in X < _]/= ltNge -(under_pvert_y vle).
  move: g2in; rewrite inE=> /orP[/eqP -> | ].
    by apply: ltW; rewrite -(strict_under_pvert_y vhe).
  move=>/oute/eqP lg2e.
  by rewrite -(under_pvert_y vg2) -lg2e left_pt_below.
have val'' : all (fun g => valid_edge g p') (s1 ++ [:: le, g2 & s2]).
  by apply/allP=> g gin; rewrite -(same_x_valid _ samex); apply: (allP val').
have strict_above:= edges_partition_strictly_above val'' rfr' p'above p'under.
move=> c1 c2 c1in c2in pp.
apply/negP=> /andP[]/andP[] /andP[] /andP[] _ belhc1 /andP[] _ rlc1p
   /andP[] abc1l llc1p.
move=>/andP[] /andP[] /andP[] _ belhc2 /andP[] _ rlc2p /andP[] ablc2 llc2p.
have c1ok : open_cell_side_limit_ok c1.
  by apply: (allP lok); rewrite ocd !mem_cat c1in.
have lebhe : le <| he.
  have [// | abs ] : below_alt le he by apply: noc.
  by move: pal; have := order_edges_viz_point' vhe vle abs (underW puh)=> ->.
have outs':
   {in sort (@edge_below R) (outgoing e), forall g, left_pt g == (point e)}.
 by move: oute; apply: sub_in1=> g; rewrite mem_sort.
have c2ok : open_cell_side_limit_ok c2.
  have noco' : {in [:: le, he & outgoing e] &, no_crossing R}.
    move: noc; apply: sub_in2=> g; rewrite !inE.
    move=> /orP[/eqP -> // | /orP[/eqP -> // | gino]].
    by rewrite !mem_cat gino orbT.
  have := opening_cells_side_limit vle vhe lebhe (underWC pal) puh noco' oute.
  by rewrite nceq; move=> /allP/(_ c2 c2in).
move: (c1ok) => /valid_high_limits -/(_ pp).
rewrite llc1p rlc1p => /(_ isT) vc1.
move: (c2ok) => /valid_low_limits -/(_ pp).
rewrite llc2p rlc2p => /(_ isT) vc2.
have highc1in : high c1 \in rcons s1 le.
  move: c1in; rewrite fceq !mem_rcons !inE => /orP[/eqP -> | ].
    by rewrite lfceq eqxx.
  by move=> ?; rewrite map_f ?orbT.
have lowc2in : low c2 = le \/ low c2 \in [seq high i | i <- rcons s' c'].
  have := opening_cells_seq_edge_shift outs' vle vhe oca_eq.
  set tmp := rcons (map _ _) _.
  have /[swap] <- : low c2 \in tmp by rewrite mem_rcons inE map_f ?orbT.
  by rewrite inE => /orP[/eqP -> // |];[left | right].
case: lowc2in=> [lowc2le | lowc2hnc].
  move: (belhc1); rewrite under_pvert_y // => belhc1'.
  move: ablc2; rewrite under_pvert_y // lowc2le; case/negP.
  have [/eqP c1lfc | c1nlfc] := boolP(c1 == lfc).
    by apply/(le_trans belhc1'); rewrite c1lfc lfceq lexx.
  have c1fc' : c1 \in fc'.
    by move: c1in; rewrite fceq mem_rcons inE (negbTE c1nlfc).
  have : high c1 <| le.
    have noc' : {in cell_edges open &, no_crossing R}.
    by move: noc; apply: sub_in2=> g gin; rewrite mem_cat gin.
    have := high_in_first_cells_below oe cbtom adj 
              (inside_box_between inbox_e) sval rfo noc' redges.
    by apply; apply: map_f.
  move/edge_below_pvert_y=>/(_ _ vc1); rewrite -lowc2le vc2=> /(_ isT) c1c2.
  by apply/(le_trans belhc1').
move: (strict_above (high c1) (low c2)).
rewrite -lfceq /s1 -map_rcons -fceq map_f //.
have -> : g2 :: s2 = [seq high c | c <- rcons s' c' ++ lc].
  by rewrite /g2 /s2; case: (s').
rewrite map_cat mem_cat lowc2hnc => /(_ isT isT); case/negP.
apply: (edge_below_from_point_under _ vc1 vc2) => //.
apply: noc.
  rewrite !mem_cat map_f ?orbT //.
  by rewrite ocd mem_cat c1in.
have := opening_cells_subset vle vhe oute; rewrite nceq=> /(_ _ c2in) /andP[].
by rewrite inE=> /orP[/eqP -> | /subo //] _; rewrite lein'.
Qed.

Lemma in_new_cell_not_in_last_old fc cc lcc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  all (edge_side_prop e) [seq high c | c <- open] ->
  all open_cell_side_limit_ok open ->
  {in opening_cells (point e) (outgoing e) le he & lc,
     forall c1 c2, o_disjoint c1 c2}.
Proof.
move=> oe aesp lok.
have [ocd [_ [_ [_ [_ [heq [leq [lein hein]]]]]]]] :=
  open_cells_decomposition_main_properties oe exi.
have [pal puh vle vhe allnct] :=
   decomposition_connect_properties rfo sval adj cbtom
             (inside_box_between inbox_e) oe.
set new_cells := opening_cells _ _ _ _.
set result_open := fc ++ new_cells ++ lc.
case oca_eq : (opening_cells_aux (point e) (sort (@edge_below _) (outgoing e))
                   le he) => [nos lno].
have adj' : adjacent_cells result_open.
  have [adjn leq'] := adjacent_opening_aux' vle vhe oute' oca_eq.
  have := opening_cells_aux_high_last vle vhe oute'.
  rewrite oca_eq /= => heq'.
  have ccn0 : rcons cc lcc  != [::] by apply/eqP/rcons_neq0.
  have nosn0 : rcons nos lno  != [::] by apply/eqP/rcons_neq0.
  have := replacing_seq_adjacent ccn0 nosn0.
  rewrite !last_rcons heq' heq leq' head_rcons leq => /(_ _ _ erefl erefl).
  have adjold : adjacent_cells (fc ++ rcons cc lcc ++ lc).
    by rewrite cat_rcons -ocd.
  move=> /(_ _ _ adjold adjn); rewrite cat_rcons /result_open.
  by rewrite /new_cells /opening_cells oca_eq cat_rcons.
have [nle nhe]:=
    higher_lower_equality oute oe erefl (exists_cell cbtom adj 
             (inside_box_between inbox_e))
         vle vhe.
move=> c1 c2; rewrite /new_cells /opening_cells oca_eq=> c1in c2in.
have [s3 [s4 lceq]] := mem_seq_split c2in.
have lceq' : lc = rcons s3 c2 ++ s4 by rewrite -cats1 -catA.
have [s1 [s2 nceq']] := mem_seq_split c1in.
have hs2 : high (last c1 s2) = he.
  move: nhe; rewrite /opening_cells oca_eq last_rcons.
  have : high (last dummy_cell (rcons nos lno)) = high lno.
    by rewrite last_rcons.
  by rewrite nceq' last_cat heq /= => -> <-.
have lt1 : p_y (point e) < pvert_y (point e) he.
  by move: puh; rewrite strict_under_pvert_y.
have lc2q : last he [seq high i | i <- s3] = low c2.
  move: adj'=> /adjacent_catW [] _.
  rewrite /new_cells /opening_cells oca_eq nceq' -catA => /adjacent_catW[] d.
  rewrite /= cat_path lceq cat_path=>/andP[] _ /andP[] _ /=.
  move=> /andP[] /eqP <- _; case: (s3) => [ // | a s'] /=.
  by rewrite last_map.
have lein' : le \in all_edges open (e :: future_events).
  by rewrite mem_cat lein.
have hein' : he \in all_edges open (e :: future_events).
  by rewrite mem_cat hein.
have lebhe : le <| he.
  have [// | abs ] : below_alt le he by apply: noc.
  by move: pal; have := order_edges_viz_point' vhe vle abs (underW puh)=> ->.
have srt : path (@edge_below _) le (sort (@edge_below _) (outgoing e)).
  apply: (sorted_outgoing vle vhe pal puh oute).
  apply: sub_in2 noc=> x; rewrite 2!inE => /orP[/eqP ->  | /orP[/eqP -> | ]] //.
  by apply: subo.
have rf' : s_right_form (last  c1 s2 :: rcons s3 c2).
(* TODO: make this one shorter. *)
  apply/allP=> c; rewrite inE=> /orP[/eqP -> {c}| cin].
    have := opening_cells_aux_right_form (underWC pal) puh vle vhe lein'
      hein' lebhe oute' noc subo' srt oca_eq.
    rewrite nceq'=> /allP /(_ (last c1 s2)); rewrite mem_cat mem_last orbT.
    by apply.
  by apply: (allP rfo); rewrite ocd lceq' !(mem_cat, inE) cin ?orbT.
have le2 : path <=%R (pvert_y (point e) he)
   [seq pvert_y (point e) (high i) | i <- rcons s3 c2].
  move: adj' => /adjacent_catW [] _.
  rewrite /new_cells /opening_cells oca_eq nceq' -catA => /adjacent_catW[] _.
  rewrite /= cat_path lceq' => /andP[] _.
  rewrite -[X in is_true X -> _]/
       (adjacent_cells ((last c1 s2 :: rcons s3 c2) ++ s4)).
  move=>/adjacent_catW[]/seq_edge_below'/(_ rf') /= => /andP[] _ + _.
  move/path_edge_below_pvert_y; rewrite hs2.
  move=> /(_ (point e)); rewrite -map_comp; apply.
  rewrite /= vhe; apply/allP=> g /mapP [c cin ->].
  apply/(seq_valid_high sval)/map_f.
  by rewrite ocd lceq' !(mem_cat, inE) cin !orbT.
have c1c2 : high c1 <| low c2.
  have := opening_cells_subset vle vhe oute => /(_ c1).
  rewrite /opening_cells oca_eq c1in => /(_ isT) /andP[ _ ].
  rewrite inE=> /orP[hc1he | hc1o].
  (* use that sorted edge_below lc, plus transitivity in this subset. *)
    have treblc : {in he :: [seq high i | i <- lc] & &,
                  transitive (@edge_below R)}.
(* This should be a general hypothesis of the lemma, established as an
   invariant. *)
    have all_left :{in he :: [seq high i | i <- lc], forall g,
           p_x (left_pt g) < p_x (point e)}.
      have lelow := decomposition_under_low_lc oe cbtom adj
                     (inside_box_between inbox_e) rfo sval.
      have adjlc' : adjacent_cells (lcc :: lc).
        move: adj; rewrite ocd => /adjacent_catW[] _.
        by move=> /adjacent_catW[] _.
      have := seq_low_high_shift => /(_ (lcc :: lc) isT adjlc') /= => - [] tmp.   move=> g; rewrite inE => /orP[/eqP -> | ].
    have lcco : lcc \in open by rewrite ocd !(mem_cat, inE) eqxx ?orbT.
    have := allP aesp (high lcc) (map_f _ lcco); rewrite /edge_side_prop.
    by rewrite -heq vhe ltNge le_eqVlt orbC lt1 /=.
    move: tmp; set s5 := rcons _ _ => tmp gin.
    have : g \in s5 by rewrite tmp inE gin orbT.
    rewrite /s5 mem_rcons inE orbC=> /orP[/mapP[c' c'in gc'] | ].
    have vc' : valid_edge (low c') (point e).
      apply/(seq_valid_low sval)/map_f.
      by rewrite ocd !(mem_cat, inE) c'in !orbT.
    have := lelow _ c'in; rewrite strict_under_pvert_y // => ga.
    move: gin=> /mapP[c'' c''in gc''].
    have c''o : c'' \in open by rewrite ocd !(mem_cat, inE) c''in !orbT.
    have := allP aesp (high c'') (map_f _ c''o); rewrite /edge_side_prop.
      rewrite (seq_valid_high sval); last by apply/map_f.
      by rewrite -gc'' gc' ltNge le_eqVlt ga orbT /=.
    move: cbtom=> /andP[] _; rewrite ocd !last_cat /= => /eqP -> /eqP ->.
  by move: inbox_e=> /andP[] _ /andP[] _ /andP[] + _.
(* finished proving all_left *)
have noc' : {in he :: [seq high i | i <- lc] &, no_crossing R}.
 apply: sub_in2 noc.
  move=> g; rewrite inE => /orP[/eqP -> // | gin].
  by rewrite ocd !(mem_cat, inE, map_cat) gin !orbT.
  have sval' : {in he :: [seq high i | i <- lc], forall g, valid_edge g (point e)}.
  move=> g; rewrite inE=> /orP[/eqP ->// | /mapP[c' c'in gc']].
  rewrite gc'; apply/(seq_valid_high sval)/map_f.
  by rewrite ocd !(mem_cat, inE) c'in !orbT.
  by have := edge_below_trans (or_intror all_left) sval' noc'.

    have adj2 : adjacent_cells (last c1 s2 :: rcons s3 c2).
      move: adj'; rewrite /result_open => /adjacent_catW[] _.
      rewrite /new_cells /opening_cells oca_eq nceq' -catA /= => /adjacent_catW[] _.
      by rewrite /= cat_path lceq' cat_path => /andP[] _ /andP[] +.
      have := seq_edge_below' adj2 rf' => /= /andP[] _.
      rewrite (path_sorted_inE treblc); last first.
      apply/allP=> g; rewrite hs2 !inE => /orP[/eqP -> | ].
      by rewrite topredE inE eqxx.
rewrite topredE inE lceq' map_cat mem_cat=> ->.
by rewrite orbT.
move=> /andP[] + _ => /allP allofthem. 
have [s3nil | s3nnil] := boolP (s3 == nil).
  by rewrite (eqP hc1he) -lc2q (eqP s3nil) edge_below_refl.
move: (allofthem (last he [seq high i | i <- s3])).
   case: (s3) s3nnil lc2q => [ // | a tl] /= _; rewrite map_rcons -cats1.
   rewrite -/((_ :: _) ++ _) mem_cat mem_last=> lc2q /(_ isT).
   by rewrite lc2q hs2 (eqP hc1he).

  have : below_alt (high c1) (low c2).
    apply: noc.
      by apply: subo.
    by rewrite ocd !(cell_edges_cat, inE, mem_cat) (map_f _ c2in) !orbT.
  move/orP=>/orP[] // abs.
  have pyec2 : p_y (point e) < pvert_y (point e) (low c2).
    apply: (lt_le_trans lt1).
    case s3q : s3 => [ | a s3'].
      by move: lc2q; rewrite s3q /= => <-.
     move: le2; rewrite le_path_sortedE => /andP[] /allP le2 _.
    set w := (last (pvert_y (point e) (high a))
                  [seq pvert_y (point e) (high i) | i <- s3']).
   suff <- : w = pvert_y (point e) (low c2).
     apply: le2; rewrite map_rcons mem_rcons inE; apply/orP/or_intror.
     by rewrite /w s3q /= mem_last.
    rewrite -lc2q /= -hs2 /w s3q /= last_map.
    by apply: last_map.
  have pyec1 : p_y (point e) = pvert_y (point e) (high c1).
    apply/esym/on_pvert/out_left_event_on=> //.
  move: pyec2; rewrite pyec1 => /pvert_y_edge_below.
  have sval' := opening_valid oute vle vhe.
  rewrite (seq_valid_high sval'); last first.
    by apply/map_f; rewrite /opening_cells oca_eq.
  rewrite (seq_valid_low sval); last first.
    by apply/map_f; rewrite ocd !(mem_cat, inE) c2in ?orbT.
  by rewrite abs => /(_ isT isT).
move=> pp; apply/negP=> /andP[] sio1 sio2.
have lho_sub : {subset le :: he :: outgoing e <=
                     all_edges open (e :: future_events)}.
  move=> g; rewrite !inE =>/orP[/eqP -> // | /orP[/eqP -> // | ]].
  by apply: subo.
have noc' : {in le :: he :: outgoing e &, no_crossing R}.
  apply: (sub_in2 _ noc)=> x; rewrite !inE => /orP[/eqP -> | /orP[/eqP -> | ]].
      by rewrite lein'.
    by rewrite hein'.
  by apply: subo.
have vp1 : valid_edge (high c1) pp.
  apply: valid_high_limits.
    apply: (allP (opening_cells_side_limit vle vhe lebhe
            (underWC pal) puh noc' oute)).  
    by rewrite /opening_cells oca_eq.
by move: sio1=> /andP[] /andP[] _ /andP[] _ -> /andP[] _ ->.
have vp2 : valid_edge (low c2) pp.
  apply: valid_low_limits.
    by apply: (allP lok); rewrite ocd !(mem_cat, inE) c2in !orbT.
  by move: sio2 => /andP[] /andP[] _ /andP[] _ -> /andP[] _ ->.
have := edge_below_pvert_y vp1 vp2 c1c2; rewrite leNgt => /negP; apply.
have lc2p : pvert_y pp (low c2) < p_y pp.
  move: (sio2) => /andP[] /andP[] _ _ /andP[] + _.
  by rewrite under_pvert_y // -ltNge.
have phc1 : p_y pp <= pvert_y pp (high c1).
  move: sio1 => /andP[] /andP[] /andP[] _ + _ _.
  by rewrite under_pvert_y.
by apply: lt_le_trans phc1.
Qed.

Let open_edge_valid x :
   x \in cell_edges open -> valid_edge x (point e).
Proof.
by rewrite /cell_edges mem_cat => /orP[] /mapP [c /(allP sval) /andP[]+ + ->].
Qed.

Lemma edge_side_prop_easy e' evs g :
  future_events = e' :: evs ->
  (g \in [:: bottom; top]) || (right_pt g == point e') -> edge_side_prop e' g.
Proof.
move=> futq /orP[gbt | ge']; rewrite /edge_side_prop.
  have : inside_box (point e').
    by apply: (allP inbox_es); rewrite futq; apply/map_f; rewrite inE eqxx.
  move=> /andP[] _ /andP[] /andP[] + + /andP[]; move: gbt.
  by rewrite !inE=> /orP[] /eqP ->; case: ifP=> //; case: ifP=> //; case: ifP.
case: ifP=> [ _ | // ].
have := on_pvert (right_on_edge g); rewrite (eqP ge') => ->.
by rewrite !lt_irreflexive.
Qed.

Lemma common_edge_side_general_case e' evs :
  future_events = e' :: evs ->
  p_x (point e) != p_x (point e') ->
  {in [seq high c | c <- open], forall g, 
     (point e <<< g) || (point e >>> g) -> edge_side_prop e' g}.
Proof.
move=> futq diffx g /mapP[c cino gq] away; rewrite /edge_side_prop.
have : end_edge (high c) (e' :: evs).
  rewrite -futq.
  move: (allP clae c cino)=> /andP[] _; rewrite /end_edge /= orbCA.
  move=> /orP[]; last by [].
  rewrite /event_close_edge -gq => /eqP eonc; rewrite -eonc in away.
  move: away; rewrite strict_nonAunder; last by apply valid_edge_right.
  rewrite under_onVstrict; last by apply valid_edge_right.
  by rewrite right_on_edge.
rewrite /end_edge /event_close_edge /= orbA -gq.
move=> /orP[/(edge_side_prop_easy futq) // | /hasP [ev2 ev2in /eqP rhc]].
case:ifP=> [vev' | //]; case:ifP=> [cbev' | _]; [ | case:ifP=> [caev' | // ]].
  rewrite rhc.
  have /orP[-> // | /andP[samex2 cmp2]] : lexPt (point e') (point ev2).
    move: sort_evs; rewrite futq /= => /andP[] _.
    rewrite path_sortedE; last first.
      exact: lexPtEv_trans.
    by move=> /andP[] /allP /(_ ev2 ev2in).
  have := on_pvert (right_on_edge g); rewrite rhc =>samey.
  have /eqP samey' := same_pvert_y vev' samex2.
  by move: cmp2; rewrite -samey -samey' ltNge le_eqVlt cbev' orbT.
have lefg : p_x (left_pt g) <= p_x (point e).
  by have [+ _] := andP (seq_valid_high sval (map_f _ cino)); rewrite -gq.
apply: (le_lt_trans lefg).
have : lexPt (point e) (point e').
  by move: sort_evs; rewrite futq /= => /andP[] + _.
by rewrite /lexPt lt_neqAle (negbTE diffx) orbF.
Qed.

Lemma outgoing_edge_side_prop e' evs :
  future_events = e' :: evs -> {in outgoing e, forall g, edge_side_prop e' g}.
Proof.
move=> futq g ino.
move: cle => /andP[] /allP /(_ _ ino) + _.
rewrite /end_edge /event_close_edge futq /= orbA.
move=> /orP[rpt_easy | /hasP[ev2 ev2in /eqP rhc]].
  by apply: (edge_side_prop_easy futq).
rewrite /edge_side_prop; case: ifP => [vce' | //].
case: ifP => [cbev' | _]; [ | case: ifP => [caev' | //]].
  have : lexPt (point e') (point ev2).
    move: sort_evs; rewrite futq /= => /andP[] _.
    rewrite path_sortedE; last first.
      exact: lexPtEv_trans.
    by move=> /andP[] /allP /(_ ev2 ev2in).
  move=> /orP[ | /andP[samex2 cmp2] ].
    by rewrite rhc.
  have := same_pvert_y vce' samex2 => samey2.
  have := on_pvert (right_on_edge g); rewrite rhc.
  move: cbev'; rewrite (eqP samey2) => + abs; rewrite ltNge le_eqVlt.
  by rewrite abs cmp2 orbT.
have [samex | diffx] := boolP (p_x (point e) == p_x (point e')).
  have yevev' : p_y (point e) < p_y (point e').
    move: sort_evs.
    rewrite futq /= /lexPtEv/lexPt lt_neqAle eq_sym=> /andP[] + _.
    by rewrite eq_sym samex.
  move: caev'.
  move: (oute ino) => leftptq.
  have vev : valid_edge g (point e).
    by rewrite valid_edge_extremities // leftptq.
  have /eqP <- := same_pvert_y vev samex.
  have /on_pvert := left_on_edge g; rewrite (eqP leftptq) => ->.
  by move=> /ltW; rewrite leNgt yevev'.
rewrite (eqP (oute ino)).
move: sort_evs.
by rewrite futq => /andP[]; rewrite /lexPtEv/lexPt (negbTE diffx) orbF.
Qed.

Lemma first_cells_edge_side c e' evs :
    future_events = e' :: evs -> c \in open -> point e >>> high c ->
    edge_side_prop e' (high c).
Proof.
move=> futq cino eabove.
have vg : valid_edge (high c) (point e).
  by apply/(seq_valid_high sval)/map_f.
have [samex | diffx] := boolP(p_x (point e) == p_x (point e')); last first.
  have := common_edge_side_general_case futq diffx (map_f _ cino).
  by apply; rewrite eabove orbT.
rewrite /edge_side_prop -(same_x_valid _ samex) vg.
rewrite under_pvert_y -1?ltNge in eabove => //.
have : pvert_y (point e') (high c) < p_y (point e'); last move=> /[dup] ye'g ->.
  rewrite -(eqP (same_pvert_y vg samex)).
  apply: (lt_trans eabove).
  move: sort_evs; rewrite futq /= /lexPtEv /lexPt => /andP[] + _.
  by rewrite (eqP samex) lt_irreflexive eqxx.
rewrite -(eqP samex).
have := allP gs (high c) (map_f _ cino); rewrite /edge_side_prop.
by rewrite vg eabove.
Qed.

Lemma last_cells_edge_side c e' evs :
    future_events = e' :: evs ->
    c \in open ->
    point e <<< high c ->
    edge_side_prop e' (high c).
Proof.
move=> futq cino ebelow.
have vg : valid_edge (high c) (point e).
  by apply/(seq_valid_high sval)/map_f.
have [samex | diffx] := boolP(p_x (point e) == p_x (point e')); last first.
  have := common_edge_side_general_case futq diffx (map_f _ cino).
  by apply; rewrite ebelow.
have vg' : valid_edge (high c) (point e') by rewrite -(same_x_valid _ samex) vg.
rewrite /edge_side_prop vg'.
case: ifP=> [ e'above | _ ]; [ | case: ifP=> [ e'below | //]]; last first.
  rewrite strict_under_pvert_y -?gq // in ebelow.
  have := allP gs (high c) (map_f _ cino).
  rewrite /edge_side_prop vg ltNge le_eqVlt ebelow ?orbT /=.
  by rewrite (eqP samex).
have := allP clae _ cino=> /andP[] _; rewrite /end_edge /= orbCA=> /orP[].
  by move=> /event_close_edge_on/onAbove/negP; rewrite ebelow.
rewrite futq /= orbA=> /orP[easycase | ].
  have := edge_side_prop_easy futq easycase.
  by rewrite /edge_side_prop -(same_x_valid _ samex) vg e'above.
move=> /hasP [ev2 ev2in /eqP rhc].
have /orP[// | /andP[samex2 cmp2] ] : lexPt (point e') (point ev2).
    move: sort_evs; rewrite futq /= => /andP[] _.
    rewrite path_sortedE; last first.
      exact: lexPtEv_trans.
    by move=> /andP[] /allP /(_ ev2 ev2in).
  by rewrite -rhc.
have := on_pvert (right_on_edge (high c)); rewrite rhc =>samey.
have /eqP samey' := same_pvert_y vg' samex2.
by move: cmp2; rewrite -samey -samey' ltNge le_eqVlt e'above orbT.
Qed.

Lemma step_keeps_edge_side_default ncs lnc lh lx:
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) :=
      opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
  close_alive_edges (fc ++ nos ++ lno :: lc) future_events ->
  edge_side future_events
    (state_open_seq {| sc_open1 := fc ++ nos;
       lst_open := lno;
       sc_open2 := lc;
       sc_closed := ncs;
       lst_closed := lnc;
       lst_high := lh;
       lst_x := lx|}).
Proof.
case oe : (open_cells_decomposition open (point e)) =>
  [[[[[fc cc] lcc] lc] le] he].
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
move=> clae'.
rewrite /state_open_seq /=.
case futq : future_events => [ // | e' events] /=.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]]
  := open_cells_decomposition_main_properties oe exi.
have lef c : c \in open -> p_x (left_pt (high c)) <= p_x (point e).
  by move=> cino; have [] := andP (seq_valid_high sval (map_f (@high _) cino)).
have ee' : lexPt (point e) (point e').
  by move: sort_evs; rewrite futq /= => /andP[].
have vle := open_edge_valid lein.
have vhe := open_edge_valid hein.
have := opening_cells_aux_high_last vle vhe (outleft_event_sort oute).
  rewrite oca_eq /= => highlnoq.
have common c : c \in lcc :: fc ++ lc ->
  edge_side_prop e' (high c).
  rewrite inE => /orP[/eqP -> | ].
    have lccino : lcc \in open by rewrite ocd !mem_cat !inE eqxx ?orbT.
    have [ _ uhe _ _ nctn]:= decomposition_connect_properties rfo sval adj
         cbtom (inside_box_between inbox_e) oe.
    apply: (last_cells_edge_side futq) => //.
    by rewrite -heq.
  rewrite mem_cat=> /orP[infc | inlc].
    have cino : c \in open by rewrite ocd !mem_cat infc.
    apply: (first_cells_edge_side futq) => //.
    by apply: (decomposition_above_high_fc oe cbtom adj
          (inside_box_between inbox_e) rfo sval infc).
  have cino : c \in open by rewrite ocd !(mem_cat, inE) inlc ?orbT.
  have [vlc vhc] :
     valid_edge (low c) (point e) /\ valid_edge (high c) (point e).
    by apply/andP; apply: (allP sval _ cino).
  suff/(last_cells_edge_side futq cino): point e <<< high c by [].
  apply: (order_edges_strict_viz_point' vlc vhc (allP rfo _ cino)).
  by apply: (decomposition_under_low_lc oe cbtom adj
               (inside_box_between inbox_e) rfo sval inlc).
apply/allP => g /mapP[c + /[dup] geq ->]; rewrite !mem_cat inE.
  rewrite -orbA (orbA (c \in nos)) orbCA orbC.
  move=> /orP[ /orP[] | ].
- by move=> cfc; apply: common; rewrite inE mem_cat cfc orbT.
- by move=> clc; apply: common; rewrite inE mem_cat   clc !orbT.
move=> cinn.
have := opening_cells_aux_subset vle vhe (outleft_event_sort oute) oca_eq.
move=> /(_ c); rewrite mem_rcons inE orbC cinn=> /(_ isT) /andP[] _.
rewrite inE=> /orP[/eqP ishe | ].
  by rewrite ishe heq; apply: common; rewrite inE eqxx.
rewrite mem_sort.
by apply: (outgoing_edge_side_prop futq).
Qed.

Lemma update_open_cell_edge_side new_op new_lsto :
  update_open_cell lsto e = (new_op, new_lsto) ->
  point e <<< high lsto ->
  point e >>> low lsto ->
  edge_side future_events (new_lsto :: new_op).
Proof.
move=> + ebelh eabl.
rewrite /update_open_cell /edge_side.
case futq : future_events => [ // | e' events] /=.
have case_lsto : edge_side_prop e' (high lsto).
  rewrite /edge_side_prop.
  case: ifP => [ vhlsto | //].
  have [samex | diffx] := boolP(p_x (point e) == p_x (point e')); last first.
    have := common_edge_side_general_case futq diffx => /(_ (high lsto)).
    rewrite map_f // ebelh /=  /edge_side_prop => /(_ isT isT).
    by rewrite vhlsto.
  have := allP clae lsto lstoin => /andP[] _; rewrite /end_edge /=.
  move=> /orP[bxe | ].
    case: ifP => [e'abovehighlsto | _].
      have := inbox_es; rewrite futq /= => /andP[] + _.
      rewrite /inside_box => /andP[] _ /andP[] /andP[] _ + /andP[] _.
      by move: bxe; rewrite !inE => /orP[] /eqP ->.
    case: ifP => [e'belowhighlsto | //].
    have := inbox_es; rewrite futq /= => /andP[] + _.
    rewrite /inside_box => /andP[] _ /andP[] /andP[] + _ /andP[] + _.
    by move: bxe; rewrite !inE => /orP[] /eqP ->.
  move=> /orP[lstoe |].
    by move: ebelh; rewrite strict_nonAunder // -(eqP lstoe) right_on_edge.
  move=> /hasP[ev2 ev2in rhl].
  rewrite (eqP rhl).
  move: ev2in; rewrite futq inE => /orP[/eqP ev2e' | ev2in].
    have xe'lsto : p_x (point e') == p_x (right_pt (high lsto)).
      by rewrite (eqP rhl) ev2e'.
    have /eqP := same_pvert_y vhlsto xe'lsto.
    rewrite (on_pvert (right_on_edge (high lsto))) (eqP rhl) ev2e'.
    case: ifP; first by move=>/[swap] ->; rewrite lt_irreflexive.
    by case: ifP=> // + _ => /[swap] ->; rewrite lt_irreflexive.
  have := sort_evs; rewrite futq /= path_sortedE; last first.
    by apply: lexPtEv_trans.
  move=>/andP[] _ /andP[] + _ => /allP /(_ ev2 ev2in).
  have := allP gs (high lsto); rewrite map_f // => /(_ isT) => side_e.
  move=>/orP[ | /andP[samex2 ev2above]].
    case: ifP => // _ ev2right.
    case: ifP=> // e'belowhighlsto.
    have : p_y (point e) < pvert_y (point e) (high lsto).
      rewrite (eqP (same_pvert_y vho samex)).
      apply: (lt_trans _ e'belowhighlsto).
      have ee' : lexPt (point e) (point e').
        by move: sort_evs; rewrite futq /= => /andP[].
      by move: ee'; rewrite /lexPt (eqP samex) lt_irreflexive eqxx /=.
    move=> keepit.
    move: side_e; rewrite /edge_side_prop vho ltNge le_eqVlt keepit orbT /=.
    by rewrite (eqP samex).
  have /eqP := same_pvert_y vhlsto samex2 => ye'e2.
  rewrite ye'e2.
  have:= (on_pvert (right_on_edge (high lsto))); rewrite (eqP rhl) => ->.
  rewrite ltNge le_eqVlt ev2above orbT /=.
  rewrite -(eqP samex).
  move: side_e; rewrite /edge_side_prop vho.
  have eunder_y : p_y (point e) < pvert_y (point e) (high lsto).
    by rewrite -strict_under_pvert_y.
  by rewrite ltNge le_eqVlt eunder_y ?orbT /=.
case ogq : (outgoing e) => [ | g1 gl].
  by move=> [] <- <- /=; rewrite andbT.
move=> oca_eq.
have -> : high new_lsto = high lsto.
  have := opening_cells_aux_high_last vlo vho (outleft_event_sort oute).
  by rewrite ogq oca_eq /=.
rewrite case_lsto /=.
have := opening_cells_aux_high vlo vho (outleft_event_sort oute).
rewrite ogq oca_eq /= -ogq => ->.
apply/allP=> g; rewrite mem_sort.
by apply: (outgoing_edge_side_prop futq).
Qed.

Lemma step_keeps_edge_side :
  edge_side future_events 
       (state_open_seq (step e (Bscan fop lsto lop cls lstc lsthe lstx))).
Proof.
move: step_keeps_invariant1=> [+ _]; rewrite /step /=.
case: ifP => [pxaway /=| /negbFE/eqP/[dup] pxhere /abovelstle palstol].
  move: step_keeps_edge_side_default.
  case oe: (open_cells_decomposition _ _) => [[[[[fc cc ] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno] def_case clae'.
  rewrite /state_open_seq /= -!catA in clae'.
  by have := def_case (cls ++ closing_cells (point e) cc)
               (close_cell (point e) lcc) he (p_x (point e)) clae'.
case: ifP=> [eabove | ebelow].
  case oe: (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      by move: adj=> /adjacent_catW[] _; case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  rewrite /state_open_seq /= => clae'.
  have := step_keeps_edge_side_default; rewrite oe' oca_eq.
  set r := (X in edge_side _ X).
  rewrite [X in close_alive_edges X](_ : _ = r); last first.
    by rewrite cat_rcons /r !catA.
  rewrite clae' /state_open_seq /= => /(_ nil dummy_cell dummy_edge 0 isT).
  by rewrite cat_rcons /r.
case futq: future_events => [ | e' events] //.
case: ifP => [ebelow_st | eonlsthe].
  case uocq : update_open_cell => [lnop lno].
  rewrite /state_open_seq /=.
  move=> clae'.
  rewrite -catA -cat_rcons; apply/allP=> g /mapP [c + gq].
  rewrite !mem_cat => /orP[cinfop | ].
    rewrite gq.
    have cino : c \in open by rewrite /open mem_cat cinfop.
    apply: (first_cells_edge_side futq) => //.
    have [lop' [lfop fopq]] : exists fop' lfop, fop = rcons fop' lfop.
      by elim/last_ind : (fop) cinfop => [ | fc' lfc _];[ | exists fc', lfc].
    have hlfop : high lfop = low lsto.
      move: adj; rewrite /open fopq cat_rcons=> /adjacent_catW[] _.
      by rewrite /= => /andP[] /eqP.
    have svalf : seq_valid fop (point e).
      by apply/allP=> c' c'in; apply: (allP sval); rewrite /open mem_cat c'in.
    have adjf : adjacent_cells fop by move: adj=> /adjacent_catW[].
    have rff : s_right_form fop.
      by apply/allP=> c' c'in; apply: (allP rfo); rewrite /open mem_cat c'in.
    have abf : point e >>> high (last dummy_cell fop).
      by rewrite fopq last_rcons hlfop.
    by have [ _ /(_ _ cinfop)]:= above_all_cells svalf adjf rff abf.
  move=>/orP[ | cinlop]; last first.
    have cino : c \in open by rewrite /open !(mem_cat, inE) cinlop !orbT.
    rewrite gq; apply: (last_cells_edge_side futq) => //.
    case lopq : lop (cinlop) => [ // | flop lop'] _.
    have lflop : low flop = high lsto.
      by move: adj; rewrite /open lopq=> /adjacent_catW[] _ /andP[]/eqP.
    have svall : seq_valid lop (point e).
      apply/allP=> c' c'in; apply: (allP sval).
      by rewrite /open !(mem_cat, inE) c'in ?orbT.
    have adjl : adjacent_cells lop.
      by move: adj; rewrite /open -cat_rcons=> /adjacent_catW[].
    have rfl : s_right_form lop.
      apply/allP=> c' c'in; apply: (allP rfo).
      by rewrite /open !(mem_cat, inE) c'in ?orbT.
    have bel : point e <<< low (head dummy_cell lop).
      by rewrite lopq /= lflop -lstheq.
    by have /(_ _ cinlop):= below_all_cells svall adjl rfl bel.
  have blsto : point e <<< high lsto by rewrite -lstheq.
  have := update_open_cell_edge_side uocq blsto palstol.
  rewrite futq /= => /andP[] eslno eslnop.
  rewrite gq mem_rcons inE => /orP[/eqP -> // | cinlnop ].
  by have := allP eslnop (high c) (map_f _ cinlnop).
rewrite /state_open_seq /=.
case oe' : (open_cells_decomposition _ (point e)) =>
  [[[[[fc' cc] lcc] lc] le] he] /=.
rewrite /update_open_cell_top /=.
have exi2 : exists2 c, c \in lsto :: lop & contains_point' (point e) c.
  exists lsto; first by rewrite inE eqxx.
  rewrite /contains_point' -lstheq.
  by move: ebelow=> /negbT; rewrite negbK andbC => ->.
have [ocd' [ctn [ctns [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
  open_cells_decomposition_main_properties oe' exi2.
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite oe' => oe.
have [ocd [_ [_ [fopfc'nct _]]]] :=
    open_cells_decomposition_main_properties oe exi.
have [_ ebellcc _ _ _] := connect_properties cbtom adj rfo sval
       (inside_box_between inbox_e) ocd fopfc'nct ctns ctn flcnct.
case ogq : (outgoing e) => [ | og1 ogs] /=.
  rewrite cats0; set nop := Bcell _ _ _ _ => clae'.
  apply/allP=> g /mapP [c + ->].
  rewrite mem_cat inE orbCA=> /orP[/eqP -> | ]; last first.
    move=>/orP[] cin.
(* TODO : big duplication here (use of below_all_cells) *)
      have cino : c \in open by rewrite /open ocd' !catA 2!mem_cat cin.
      apply: (first_cells_edge_side futq) => //.
      by have := decomposition_above_high_fc oe cbtom adj
           (inside_box_between inbox_e) rfo sval cin.
    have lcsub: {subset lc <= open}.
      by move=> x xin; rewrite /open ocd' !(mem_cat, inE) xin ?orbT.
    apply: (last_cells_edge_side futq); first by apply: lcsub.
    have svall : seq_valid lc (point e).
      by apply/allP=> c' c'in; apply: (allP sval); apply: lcsub.
    have adjl : adjacent_cells lc.
      move: adj; rewrite /open ocd' -cat_rcons.
      by do 3 move=> /adjacent_catW[] _.
    have rfl : s_right_form lc.
      by apply/allP=> c' c'in; apply: (allP rfo); apply: lcsub.
    have bel : point e <<< low (head dummy_cell lc).
      move: (cin); case lcq : lc => [// | flc lc'] _ /=.
      move: adj; rewrite /open ocd' lcq /=.
      do 3 move=> /adjacent_catW[] _.
      rewrite /= => /andP[] /eqP + _ => lfcq.
      by rewrite -lfcq.
    by have /(_ _ cin):= below_all_cells svall adjl rfl bel.
  rewrite /= heq.
  apply: (last_cells_edge_side futq) => //.
  by rewrite /open ocd' !(mem_cat, inE) eqxx !orbT.
rewrite -ogq /=.
case oca_eq : (opening_cells_aux _ _ _ _) => [nops lnop] /=.
have hein' : he \in cell_edges open.
  by rewrite /open cell_edges_cat mem_cat hein orbT.
move=> clae'.
have := step_keeps_edge_side_default; rewrite oe.
have inlsto : contains_point (point e) lsto.
  rewrite /contains_point  -leNgt ltW; last first.
    by rewrite ltNge; exact: palstol.
  by move: ebelow=> /negbFE; rewrite lstheq.
have fc'0 : fc' = [::].
  case fc'q : fc' => [// | fc'i fc2].
  move: ocd'; rewrite fc'q /= => - [] lstoisfc'i _.
  by move: (all_nct lsto); rewrite inlsto fc'q lstoisfc'i inE eqxx=> /(_ isT).
have lelsto : le = low lsto.
  have [ fopq | [fop' [lfop fopq]]] :
      fop = nil \/ exists fop' lfop, fop = rcons fop' lfop.
      elim/last_ind: (fop) => [| fop' lfop]; first by left.
      by right; exists fop', lfop.
    move: ocd'; rewrite -cat_rcons fc'0 /= => lstohead.
    suff : lsto = head lcc cc by move=> ->.
    by rewrite -[LHS]/(head lsto (lsto :: lop)) lstohead; case: (cc).
  move: adj; rewrite /open ocd' fopq fc'0 cat_rcons /=.
  move=> /adjacent_catW[] _ it.
  move: ocd'; rewrite fc'0 /=; move: it=> /[swap] <- /andP[] /eqP <- _.
  apply/esym; rewrite leq.
  move: adj; rewrite /open ocd fc'0 cats0 fopq cat_rcons=>/adjacent_catW[] _.
  by case: (cc) => [ | cc0 cc'] /andP[] /eqP ->.
rewrite lelsto oca_eq /= /state_open_seq /= =>
  /(_ nil dummy_cell dummy_edge 0).
move: clae'; rewrite -futq !catA => clae'.
by move=> /(_ clae'); rewrite futq /=.
Qed.

Lemma step_keeps_disjoint_open ev open closed open' closed' events :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point ev) ->
  seq_valid open (point ev) ->
  s_right_form open ->
  {in [seq low c | c <- open] ++ [seq high c | c <- open] ++
      outgoing ev &, forall e1 e2, inter_at_ext e1 e2} ->
  {in open &, disjoint_open_cells R} ->
  out_left_event ev ->
  all open_cell_side_limit_ok open ->
  edge_side (ev :: events) open ->
  close_alive_edges open (ev :: events) ->
  all (fun x => lexPtEv ev x) events ->
  step ev open closed = (open', closed') ->
  {in open' &, disjoint_open_cells R}.
Proof.
(*
move=> cbtom adj inbox_e sval rfo /[dup] noc /inter_at_ext_no_crossing noc'
  disj outlefte cellsok edge_side_open clae lexev.
have noc4 : {in cell_edges open ++ outgoing ev &, no_crossing R}.
   by move=> g1 g2 g1in g2in; apply: noc'; rewrite catA.
set ctxt := [seq low c | c <- open] ++ [seq high c | c <- open] ++ outgoing ev.
rewrite /step.
case oe: (open_cells_decomposition open (point ev)) => [[[[fc cc] lc] le] he].
have ocd := decomposition_preserve_cells oe.
have osub : {subset sort (@edge_below R) (outgoing ev) <= ctxt}.
  move=> g.
  have -> := perm_mem (permEl (perm_sort (@edge_below R) (outgoing ev))).
  by move=> gin; rewrite /ctxt !mem_cat gin !orbT.
have := l_h_in_open cbtom adj inbox_e.
rewrite oe /= => -[cle [che [clein [chein [/esym cleq /esym cheq]]]]].
have [eale euhe] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
set oc := opening_cells _ _ _ _.
have lein : le \in ctxt.
  by rewrite /ctxt !mem_cat cleq map_f.
have hein : he \in ctxt.
  by rewrite /ctxt !mem_cat cheq map_f ?orbT.
have vle : valid_edge le (point ev).
  by move: (seq_valid_low sval (map_f _ clein)); rewrite cleq.
have vhe : valid_edge he (point ev).
  by move: (seq_valid_high sval (map_f _ chein)); rewrite cheq.
have lowhigh : le <| he.
  have noc2 : {in [seq low c | c <- open] ++
                 [seq high c | c <- open] &, no_crossing R}.
    by move: noc'; apply: sub_in2 => g gin; rewrite catA mem_cat gin.
  by have lowhigh := open_cells_decomposition_low_under_high 
                   noc2 cbtom adj inbox_e sval rfo oe.
have outlefts :
   {in sort (@edge_below R) (outgoing ev), forall g, left_pt g == point ev}.
  move=> g.
  have -> := perm_mem (permEl (perm_sort (@edge_below R) (outgoing ev))). 
  by apply: outlefte.
have noc2 : {in le :: he :: outgoing ev &, no_crossing R}.
  move: noc'; apply: sub_in2=> g; rewrite !inE => /orP [/eqP -> | ].
    by rewrite cleq mem_cat map_f.
  move=> /orP [/eqP -> | ].
    by rewrite cheq !mem_cat map_f ?orbT.
  by move=> gin; rewrite !mem_cat gin ?orbT.
have srt := sorted_outgoing vle vhe eale euhe outlefte noc2.
have clae' : close_alive_edges fc events.
  apply/allP=> c cin; suff symcl : forall b, end_edge (any_edge b c) events.
    by apply/andP; split;[apply: (symcl true) | apply: (symcl false)].
  move=> b.
  have cin' : c \in open by rewrite ocd !mem_cat cin ?orbT.
  have /orP[] : end_edge (any_edge b c) (ev :: events).
      by case: b; rewrite /any_edge; move: (allP clae _ cin') => /andP[].
    by move=> it; apply/orP; left; exact it.
  move=> /hasP[ev' ev'in geq].
  move: ev'in; rewrite inE=> /orP[/eqP evev' | ev'in]; last first.
    by apply/orP; right; apply/hasP; exists ev'.
  suff : false by [].
  move: geq; rewrite evev' => {ev' evev'} geq.
  have evon : point ev === any_edge b c by rewrite -(eqP geq) right_on_edge.
  have vb : valid_edge (any_edge b c) (point ev) by move: evon=> /andP[].
  have vb' : valid_edge (any_edge (~~ b) c) (point ev).
    by move: sval => /allP /(_ c cin')=> /andP[]; case: (b).
  have : (point ev >>= (any_edge b c)) && (point ev <<= (any_edge b c)).
    by rewrite (under_onVstrict vb) evon /= andbT (strict_nonAunder vb) evon.
  move=> /andP[ab bel].
  have edgeo : any_edge true c <| any_edge false c.
    by move: rfo => /allP /(_ _ cin').
  have := decomposition_not_contain rfo sval adj cbtom inbox_e oe.
  move=> /(_ c); rewrite cin /contains_point /= => /(_ isT); case.
  case beq : b.
    have := order_edges_viz_point' vb vb'; rewrite beq => /(_ edgeo).
    rewrite -beq bel beq => /(_ isT) => underh.
    move: ab; rewrite beq /any_edge => ->; exact underh.
  have : point ev >>= any_edge (~~b) c.
    have := order_edges_strict_viz_point' vb' vb; rewrite beq => /(_ edgeo).
    have [_ abs| // ] := boolP (point ev <<< any_edge (~~ false) c).
    by case/negP: ab;rewrite beq abs.
  by move: bel; rewrite beq /= => -> ->.
set fc_edges := cell_edges fc.
set lc_edges := cell_edges lc.
set extra_bot := Bcell nil nil bottom bottom.
have [botc [otail openeq]] : exists botc otail, open = botc :: otail.
  move: cbtom=>/andP[]/andP[]; case openeq: open => [// | botc otail] /= _.
  by exists botc; exists otail.
have lowbot : low botc = bottom.
  by move: cbtom=> /andP[]/andP[]; rewrite openeq /= => _ /eqP.
have adje : adjacent_cells (extra_bot :: open).
  by rewrite openeq /= lowbot eqxx /=; move: adj; rewrite openeq /=.
have botfc : fc != nil -> head dummy_cell fc = botc.
  have : head dummy_cell open = botc by rewrite openeq.
  by rewrite ocd; case: (fc) => [ | ? ?].
have botfc' : fc != nil -> fc = botc :: behead fc.
  by move=> fcn0; rewrite -(botfc fcn0); case: (fc) fcn0.
have lowbotc : low botc = bottom.
  by move: adje; rewrite openeq /= => /andP[]/eqP ->.
have := l_h_c_decomposition oe (exists_cell cbtom adj inbox_e).
move=> -[] /eqP/esym lehcc [] _ ccn0.
have ccdec : cc = head dummy_cell cc :: behead cc by case: (cc) ccn0.
have higfc : fc != nil -> high (last dummy_cell fc) = le. (* to be used *)
  elim/last_ind : (fc) ocd adje => [// |s c' _] /= ocd + _.
  rewrite ocd cat_path last_rcons.
  by rewrite ccdec /= last_rcons lehcc => /andP[] _ /andP[] /eqP -> _. 
have lowvert : {in fc_edges, forall g, pvert_y (point ev) g < p_y (point ev)}.
  suff highs : {in [seq high c | c <- fc],
                 forall g, pvert_y (point ev) g < p_y (point ev)}.
    move=> g; rewrite mem_cat=>/orP[] gin; last by apply: highs.
    have fcn0 : fc != nil by move: gin; case: (fc).
    have : g \in rcons [seq low c| c <- fc] le.
      by rewrite mem_rcons inE gin orbT.
    have -> : le = high (last dummy_cell fc).
      move: adje; rewrite /= ocd.
      rewrite cat_path => /andP[] _.
      have -> : last dummy_cell fc = last extra_bot fc by case: (fc) fcn0.
      by rewrite lehcc ccdec => /andP[]/eqP/esym.
    rewrite seq_low_high_shift; last first.
        by move: (adj); rewrite ocd=> /adjacent_catW[].
      by apply/eqP=> abs; move: gin=>/mapP[]; rewrite abs.
    rewrite inE=> /orP[/eqP -> | ]; last by apply: highs.
    by rewrite botfc // lowbotc (pvert_y_bottom inbox_e).
  have : sorted <=%R [seq pvert_y (point ev) (high c) | c <- extra_bot::open].
    apply adjacent_right_form_sorted_le_y => //=.
      rewrite andbb; apply/andP; split=> //.
      by apply: (inside_box_valid_bottom_top inbox_e)=> //; rewrite inE eqxx.
    by rewrite edge_below_refl.
  rewrite /= => pathlt.
  move=> g /mapP[c cin gceq].
  have [s1 [s2 fceq]] := mem_seq_split cin.
  have vertle : pvert_y (point ev) le < p_y (point ev).
    have [+ _]:= l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
    rewrite under_pvert_y; last first.
      rewrite lehcc ccdec; apply/(seq_valid_low sval)/map_f.
      by rewrite ocd ccdec !mem_cat /= inE eqxx ?orbT.
    by rewrite ltNge.
  elim/last_ind : (s2) fceq => [ | s2' ls2 _] fceq.
    rewrite gceq.
    move: adje; rewrite ocd fceq /=.
    rewrite cat_path ccdec /= cats1 last_rcons => /andP[] _ /andP[] /eqP higheq.
    by rewrite higheq -lehcc => _.
  move: pathlt; rewrite ocd fceq map_cat cat_path=> /andP[] + _.
  rewrite map_cat cat_path => /andP[] _ /= => /andP[] _.
  rewrite map_rcons path_sortedE; last by apply: le_trans.
  move=>/andP[] + _ => /allP /(_ (pvert_y (point ev) (high ls2))).
  rewrite mem_rcons inE eqxx -gceq => /(_ isT) first_part.
  apply: (le_lt_trans first_part) => {first_part}.
  move: (adje);  rewrite ocd /= fceq cat_path => /andP[] _.
  rewrite -[c :: _]/([:: c] ++ _) catA -rcons_cat last_rcons ccdec /=.
  by move=> /andP[]/eqP -> _; rewrite -lehcc.
have fcopen : {subset fc <= open}.
  by move=> g gin; rewrite ocd !mem_cat gin ?orbT.
have valfc : {in fc_edges, forall g, valid_edge g (point ev)}.
  by move=> g; rewrite /fc_edges mem_cat => /orP[]/mapP[c cin ->];
    case: (andP (allP sval c _))=> //; rewrite ocd !mem_cat cin ?orbT.
(* TODO : This easy proof indicates that edge_side_prop could be made
  much easier, only the top part being important. *)
have fcedgesright: {in fc_edges, forall g, p_x (point ev) < p_x (right_pt g)}.
  move=> g; rewrite mem_cat => gin.
  have /orP[bottop | ] : end_edge g events.
      by move: gin=> /orP[] /mapP[c cin ->]; move: (allP clae' _ cin)=>/andP[].
    move: inbox_e => /andP[] _ /andP[] /andP[] _ + /andP[] _.
    by move: bottop; rewrite !inE=> /orP[] /eqP ->.
  move=> /hasP [e' e'in /eqP /[dup]geq ->].
  have : lexPt (point ev) (point e') by apply: (allP lexev).
  move=>/orP[ // | ] /andP[] /eqP xs ys.
  suff /eqP abs : pvert_y (point ev) g == p_y (point e').
    have:= lowvert g; rewrite /fc_edges mem_cat gin abs => /(_ isT).
    by rewrite ltNge le_eqVlt ys orbT.
  have vg : valid_edge g (point ev) by apply: valfc; rewrite /fc_edges mem_cat.
  have := pvert_on vg => ievg.
  move: (right_on_edge g); rewrite geq => ev'g.
  by apply: (on_edge_same_point ievg ev'g) => /=; rewrite xs eqxx.
have noc3 : {in fc_edges &, no_crossing R}.
  move: noc'; apply: sub_in2 => g.
  by rewrite ocd !map_cat !mem_cat => /orP[] ->; rewrite ?orbT /=.
have tr : {in fc_edges & &, transitive (@edge_below R)}.
  by apply: (edge_below_trans _ valfc) => //; first by left; [].

have lowfc : {in fc_edges, forall g, g <| le}.
  suff highs : {in [seq high c | c <- fc], forall g, g <| le}.
    move=> g; rewrite mem_cat=>/orP[] gin; last by apply: highs.
    have fcn0 : fc != nil by move: gin; case: (fc).
    have : g \in rcons [seq low c| c <- fc] le.
      by rewrite mem_rcons inE gin orbT.
    have -> : le = high (last dummy_cell fc).
      move: adje; rewrite /= ocd.
      rewrite cat_path => /andP[] _.
      have -> : last dummy_cell fc = last extra_bot fc by case: (fc) fcn0.
      by rewrite lehcc ccdec => /andP[]/eqP/esym.
    rewrite seq_low_high_shift; last first.
        by move: (adj); rewrite ocd=> /adjacent_catW[].
      by apply/eqP=> abs; move: gin=>/mapP[]; rewrite abs.
    rewrite inE=> /orP[/eqP -> | inh ]; last by rewrite higfc // highs.
    rewrite (botfc fcn0).
    have := seq_edge_below' adj rfo; rewrite /= ocd (botfc' fcn0) [head _ _]/=.
    rewrite map_cat cat_path => /andP[+ sndpart].
    rewrite (path_sorted_inE tr).
      rewrite -(botfc' fcn0) => /andP[fp sp]; apply: (allP fp).
      by apply/map_f/last_in_not_nil.
    rewrite allcons; apply/andP; split.
      suff it : low botc \in fc_edges by exact it.
      by rewrite /fc_edges mem_cat map_f // botfc' // inE eqxx.
    apply/allP=> x xin; rewrite /fc_edges.
    suff it : x \in ([seq low c | c <- fc] ++ [seq high c | c <- fc]) by exact it.
    by rewrite mem_cat; move: xin; rewrite -botfc' // orbC //= => ->.
  move=> g gin.
  have := seq_edge_below' adj rfo; rewrite [X in head _ (map _ X)]openeq /= lowbot.
  rewrite ocd map_cat cat_path=> /andP[] + _. (* tailcond. *)
  move: gin=> /mapP[c cin geq].
  have [fch [fct ]] := mem_seq_split cin.
  rewrite -[_ :: _]/([:: _] ++ _) catA => fcteq.
  rewrite fcteq map_cat cat_path => /andP[] _.
  rewrite cats1 map_rcons last_rcons.
  rewrite (path_sorted_inE tr); last first. 
    apply/allP=> x xin; rewrite /fc_edges.
    suff it : x \in ([seq low c | c <- fc] ++ [seq high c | c <- fc]) by exact it.
    move: xin; rewrite inE mem_cat=> /orP[/eqP -> | int ].
      by rewrite map_f ?orbT.
    by rewrite fcteq /= !map_cat !mem_cat /= int ?orbT.
  have [fcteq' | [fct' [lf fcteq']]] : fct = nil \/ (exists fct' lf, fct = rcons fct' lf).
    elim/last_ind: (fct) => [ | fct' lf _];[by left | by right; exists fct', lf].
    move=> _.
    move: adje; rewrite /= ocd fcteq fcteq' cats0 ccdec.
    rewrite cat_cons cats1 cat_path => /andP[] _ /= => /andP[]/eqP + _.
    rewrite last_rcons geq -lehcc => ->; by rewrite edge_below_refl.
  move=> /andP[] /allP /(_ (high lf)) + _.
  rewrite -geq map_f; last by rewrite fcteq' mem_rcons inE eqxx.
  move=> /(_ isT) => ghlf.
  move: adje; rewrite /= ocd fcteq fcteq' ccdec.
  rewrite cat_cons cat_path => /andP[] _ /= => /andP[]/eqP + _.
  by rewrite last_cat last_rcons -lehcc => <-.
have ocdisjlc : {in oc & lc, forall c1 c2, o_disjoint c1 c2}.
  exact: (in_new_cell_not_in_last_old oe cbtom adj inbox_e rfo sval
     outlefte noc4 edge_side_open cellsok).
have ocdisjfc : {in oc & fc, forall c1 c2, o_disjoint c1 c2}.
  move=> c1 c2 c1in c2in p; apply/andP=> -[pino pinf].
  have := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  move=> /[dup] ib [] ibl ibh.
  move: (pino) => /andP[] /[dup] invert /andP[] inverth invertl _.
  have pxlt : {in [seq high c | c <- fc],
    forall g, p_x (point ev) < p_x (right_pt g)}.
    by move=> g gin; apply: fcedgesright; rewrite /fc_edges mem_cat gin orbT.
  have := in_new_cell_not_in_first_old oe cbtom adj inbox_e rfo sval outlefte
    noc4 cellsok pxlt.
  by move=> /(_ c2 c1 c2in c1in p); rewrite /o_disjoint pino pinf.
move=> [] <- _.
suff main : {in predU (mem oc) (mem (fc ++ lc)) &, disjoint_open_cells R}.
  by move=> c1 c2 inc1 inc2; apply: main;[move: inc1 | move: inc2];
  rewrite !(inE, mem_cat) orbCA.
apply: add_new.
- exact: o_disjointC.
- case oca_eq : (opening_cells_aux (point ev) 
                      (sort (@edge_below _) (outgoing ev)) le he) => [s' c'].
  have ocq : oc = rcons s' c' by rewrite /oc/opening_cells oca_eq.
- have := opening_cells_aux_disjoint eale euhe lein hein lowhigh
              vle vhe osub noc' outlefts srt oca_eq.
  by rewrite ocq.
- move=> new old nin; rewrite mem_cat=>/orP[] oin.
    by apply: ocdisjfc.
  by apply: ocdisjlc.
move=> c1 c2 c1in c2in.
by apply: disj; rewrite ocd !mem_cat orbCA -mem_cat; apply/orP; right.
Qed.
*)

Lemma step_keeps_disjoint ev open closed open' closed' events :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point ev) ->
  seq_valid open (point ev) ->
  s_right_form open ->
  {in [seq low c | c <- open] ++ [seq high c | c <- open] ++
      outgoing ev &, forall e1 e2, inter_at_ext e1 e2} ->
  {in open &, disjoint_open_cells R} ->
  {in closed &, @disjoint_closed_cells R} ->
  {in open & closed, @disjoint_open_closed_cells R} ->
  {in closed, forall c, right_limit c <= p_x (point ev)} ->
  out_left_event ev ->
  all open_cell_side_limit_ok open ->
  edge_side (ev :: events) open ->
  close_alive_edges open (ev :: events) ->
  all (fun x => lexPtEv ev x) events ->
  step ev open closed = (open', closed') ->
  {in closed' &, disjoint_closed_cells R} /\
  {in open' & closed', disjoint_open_closed_cells R}.
Proof.
move=> cbtom adj inbox_e sval rfo noc doc dcc docc rtl out_e sok
  edge_side_open clae lexev.
rewrite /step.
case oe : (open_cells_decomposition open (point ev)) =>
   [[[[fc  cc] lc] le] he] [<- <-].
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
    lhc_dec cbtom adj inbox_e oe.
have svalcc : seq_valid cc (point ev).
  by apply/allP=> c cin; apply: (allP sval); rewrite ocd !mem_cat cin !orbT.
have adjcc : adjacent_cells cc.
  by move: adj; rewrite ocd=>/adjacent_catW[] _ /adjacent_catW[].
have rfocc : s_right_form cc.
  by apply/allP=> c cin; apply: (allP rfo); rewrite ocd !mem_cat cin !orbT.
have allcont : all (contains_point (point ev)) cc.
  by apply/allP=> c; apply: (open_cells_decomposition_contains oe).
have closed_map : closing_cells (point ev) cc =
       [seq close_cell (point ev) c | c <- cc] by [].
have ccok : all open_cell_side_limit_ok cc.
  by apply/allP=> c cin; apply: (allP sok); rewrite ocd !mem_cat cin !orbT.
have : all (@closed_cell_side_limit_ok _) (closing_cells (point ev) cc).
  have [pal puh] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  apply: (closing_cells_side_limit' rfocc svalcc adjcc ccok allcont).
    by rewrite ccq /= leq.
  by rewrite ccq /= -heceq heq.
rewrite [X in all _ X]closed_map=> /allP cl_sok.
have oldcl_newcl :
  {in closed & closing_cells (point ev) cc, disjoint_closed_cells R}.
  move=> c1 c2 c1in.
  rewrite closed_map => /mapP[c2' c2'in c2eq].
  have c2'open : c2' \in open by rewrite ocd !mem_cat c2'in orbT.
    have vc2 : valid_cell c2' (point ev) by apply/andP/(allP sval).
  right; rewrite /c_disjoint=> q; apply/negP=> /andP[inc1 inc2].
  rewrite c2eq in inc2.
  case: (negP (docc c2' c1 c2'open _ q)) => //; rewrite inc1 andbT.
  apply:(close'_subset_contact vc2 _ inc2).
  by move: (cl_sok c2); rewrite c2eq; apply; apply: map_f.
split.
  move=> c1 c2; rewrite !mem_cat.
  move=> /orP[c1old | c1new] /orP[c2old | c2new]; first by apply: dcc.
      by apply: oldcl_newcl.
    by apply: c_disjoint_eC; apply: oldcl_newcl.
  rewrite closed_map in c1new c2new.
  move: c1new c2new => /mapP[c1' c1'in c1eq] /mapP[c2' c2'in c2eq].
  have c1'open : c1' \in open by rewrite ocd !mem_cat c1'in orbT.
  have c2'open : c2' \in open by rewrite ocd !mem_cat c2'in orbT.
  have vc1 : valid_cell c1' (point ev) by apply/andP/(allP sval).
  have vc2 : valid_cell c2' (point ev) by apply/andP/(allP sval).
  have [/eqP c1c2 | c1nc2] := boolP(c1' == c2').
    by left; rewrite c1eq c2eq c1c2.
  right=> q; apply/negP=> /andP[inc1 inc2].
  have := doc c1' c2'; rewrite ocd !mem_cat c1'in c2'in !orbT.
  move=> /(_ isT isT) [/eqP |]; first by rewrite (negbTE c1nc2).
  move=> /(_ q) /negP [].
  rewrite c1eq in inc1; rewrite c2eq in inc2.
  rewrite (close'_subset_contact vc1 _ inc1); last first.
    by apply: cl_sok; apply: map_f.
  rewrite (close'_subset_contact vc2 _ inc2) //.
  by apply: cl_sok; apply: map_f.
have vle : valid_edge le (point ev).
  have:= (proj1 (andP (allP svalcc lec _))).
  by rewrite ccq inE eqxx leq; apply.
have vhe : valid_edge he (point ev).
  have:= (proj2 (andP (allP svalcc hec _))).
  by rewrite ccq heceq mem_last -heq -heceq; apply.
move=> c1 c2; rewrite !mem_cat orbCA => /orP[c1newo | c1old] c2in.
  have rlc2 : right_limit c2 <= p_x (point ev).
    move: c2in => /orP[/rtl // | ].
    rewrite closed_map=> /mapP[c2' c2'in ->].
    by rewrite close_cell_right_limit //; apply/andP/(allP svalcc).
  move=> q; rewrite inside_open'E inside_closed'E; apply/negP.
  move=> /andP[] /andP[] _ /andP[] _ /andP[] + _
     /andP[] _ /andP[] _ /andP[] _ +.
  rewrite (opening_cells_left out_e vle vhe c1newo) => evq qrlc2.
  by move: rlc2; rewrite leNgt=> /negP[]; apply (lt_le_trans evq).
have c1open : c1 \in open by rewrite ocd !mem_cat orbCA c1old orbT.
move: c2in=> /orP[c2old | ].
   apply: docc; by rewrite // ocd !mem_cat orbCA c1old orbT.
rewrite closed_map=> /mapP[c2' c2'in c2eq] q; apply/negP=> /andP[] inc1 inc2.
have c2'open : c2' \in open by rewrite ocd !mem_cat c2'in !orbT.
have [c1eqc2 | disjc1c2] := doc _ _ c1open c2'open.
  case: (decomposition_not_contain rfo sval adj cbtom inbox_e oe c1old).
  rewrite c1eqc2.
  by apply: (open_cells_decomposition_contains oe).
move: (disjc1c2 q); rewrite inc1 //.
have vc2 : valid_cell c2' (point ev) by apply/andP/(allP sval).
rewrite c2eq in inc2.
rewrite (close'_subset_contact vc2 _ inc2) //.
by apply: cl_sok; apply: map_f.
Qed.

Lemma left_limit_closing_cells (cc : seq cell) (p : pt) :
  adjacent_cells cc -> seq_valid cc p ->
  p >>> low (head_cell cc) -> p <<< high (last_cell cc) ->
  all (contains_point p) cc ->
  [seq left_limit i | i <- closing_cells p cc] = [seq left_limit i | i <- cc].
Proof.
move=> adj sval pale puhe allcont.
rewrite /closing_cells.
rewrite -map_comp; rewrite -eq_in_map /close_cell => -[] ls rs lo hi cin /=.
move: (allP sval _ cin) => /= /andP[] vlo vhi.
by rewrite (pvertE vlo) (pvertE vhi).
Qed.

Lemma step_keeps_injective_high e open closed open2 closed2 :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  s_right_form open ->
  out_left_event e ->
  uniq (outgoing e) ->
  {in open, forall c, lexPt (left_pt (high c)) (point e)} ->
  step e open closed = (open2, closed2) ->
  {in open &, injective (@high R)} ->
  {in open2 &, injective (@high R)}.
Proof.
move=> cbtom adj inbox_e sval rfo out_e uout lexp + inj_high; rewrite /step.
case oe : open_cells_decomposition => [[[[fc cc] lc] le] he].
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
have leco : lec \in open by rewrite ocd ccq !mem_cat !inE eqxx !orbT.
have heco : hec \in open by rewrite ocd ccq heceq !mem_cat mem_last !orbT.
have vle : valid_edge le (point e).
  by rewrite -leq; apply/(seq_valid_low sval)/map_f.
have vhe : valid_edge he (point e).
  by rewrite -heq; apply/(seq_valid_high sval)/map_f.
have dupcase c1 c2 : (c1 \in fc) || (c1 \in lc) ->
   c2 \in opening_cells (point e) (outgoing e) le he ->
   high c1 = high c2 -> c1 = c2.
  move=> c1in c2in hc1c2.
  have v1 : valid_edge (high c1) (point e).
    move: sval=> /allP /(_ c1); rewrite ocd !mem_cat orbCA c1in orbT.
    by move=> /(_ isT) /andP[].
  have v2 : valid_edge (high c2) (point e).
    have /andP[ _ ] := opening_cells_subset vle vhe out_e c2in.
    rewrite inE=> /orP[/eqP -> // | ].
    by have := opening_valid out_e vle vhe => /allP /(_ _ c2in) /andP[].
  have : point e <<< high c1 \/ point e >>> high c1.
    move: c1in=> /orP[] c1in.
      right.
      by have := decomposition_above_high_fc oe cbtom adj inbox_e rfo sval c1in.
    left.
    have [s1 [s2 lcq]] := mem_seq_split c1in.
    case s2q : s2 => [ | c1' s2'].
      move: inbox_e=> /andP[] /andP[] _ + _.
      suff -> : high c1 = top by [].
      by move: cbtom=> /andP[] _ /eqP; rewrite ocd lcq s2q /= !last_cat /=.
    have c1'in : c1' \in lc by rewrite lcq s2q mem_cat !inE eqxx !orbT.
    have := decomposition_under_low_lc oe cbtom adj inbox_e rfo sval c1'in.
    suff -> : high c1 = low c1' by [].
    move: adj; rewrite /adjacent_cells ocd=> /sorted_catW /andP[] _.
    move=> /sorted_catW /andP[] _; rewrite lcq s2q.
    by move=> /sorted_catW /andP[] _ /= /andP[] /eqP.
  have /andP[lows ] := opening_cells_subset vle vhe out_e c2in.
  rewrite inE => /orP[/eqP hc1he | ]; last first.
    rewrite hc1c2 => /out_e/eqP <-.
    move=> [ | ].
      rewrite strict_nonAunder; last first.
        by apply valid_edge_extremities; rewrite eqxx ?orbT.
      by rewrite left_on_edge.
    rewrite under_onVstrict ?left_on_edge //.
    by apply valid_edge_extremities; rewrite eqxx ?orbT.
  have c1hec : c1 = hec.
    apply: inj_high => //.
      by rewrite ocd !mem_cat orbCA c1in orbT.
    by rewrite hc1c2 hc1he.
  have := decomposition_not_contain rfo sval adj cbtom inbox_e oe c1in.
  have heccc : hec \in cc by rewrite ccq heceq mem_last.
  have := open_cells_decomposition_contains oe heccc.
  by rewrite c1hec => ->.
have henout : he \notin outgoing e.
  apply/negP=> /out_e /eqP abs.
  by have := lexp hec heco; rewrite heq abs lexPt_irrefl.
move=> [<- _] c1 c2; rewrite !mem_cat orbCA=> /orP[] c1in; last first.
  rewrite orbCA=> /orP[] c2in; last first.
    by apply: inj_high; rewrite ocd !mem_cat orbCA ?c1in ?c2in orbT.
  by apply: dupcase _ _ c1in c2in.
rewrite orbCA=> /orP[] c2in; last first.
  move/esym=> tmp; apply/esym; move: tmp.
  by apply: dupcase _ _ c2in c1in.
have : uniq (rcons (sort (@edge_below _) (outgoing e)) he).
  by rewrite rcons_uniq mem_sort henout sort_uniq.
by rewrite -(opening_cells_high vle vhe out_e) => /uniq_map_injective; apply.
Qed.

Lemma right_limit_close_cell p c :
  valid_edge (low c) p -> valid_edge (high c) p ->
  right_limit (close_cell p c) = p_x p.
Proof.
move=> vlc vhc; rewrite /close_cell /right_limit.
rewrite !pvertE //=.
by case: ifP; case: ifP.
Qed.

Lemma step_keeps_closed_to_the_left ev open closed open' closed' :
  cells_bottom_top open ->
  adjacent_cells open ->
  seq_valid open (point ev) ->
  inside_box (point ev) ->
  s_right_form open ->
  step ev open closed = (open', closed') ->
  {in closed, forall c, right_limit c <= p_x (point ev)} ->
  {in closed', forall c, right_limit c <= p_x (point ev)}.
Proof.
move=> cbtom adj sval inbox_e rfo.
rewrite /step.
case oe: (open_cells_decomposition open (point ev)) =>
      [[[[fc cc] lc] le] he] [_ <-].
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
have ccsub : {subset cc <= open}.
  by rewrite ocd=> c; rewrite !mem_cat orbCA=> ->.
have adjcc : adjacent_cells cc.
  by rewrite ocd in adj; move: adj => /adjacent_catW[] _ /adjacent_catW[].
have svalcc : seq_valid cc (point ev).
  by apply/allP=> c cin; apply/(allP sval)/ccsub.
have [al uh] :
  point ev >>> (low (head dummy_cell cc)) /\
  point ev <<< (high (last dummy_cell cc)).
  rewrite ccq /= -heceq leq heq.
  by apply: (l_h_above_under_strict cbtom adj inbox_e sval rfo oe).
have allcont : all (contains_point (point ev)) cc.
  by apply/allP=> c; apply: (open_cells_decomposition_contains oe).
move=> rtl c; rewrite mem_cat=> /orP[].
  by apply: rtl.
move=> /mapP[c' c'in ceq].
rewrite ceq (close_cell_right_limit) //.
by apply/andP/(allP svalcc).
Qed.

Lemma left_limit_close_cell p c : 
   left_limit (close_cell p c) = left_limit c.
Proof.
rewrite /close_cell.
by do 2 (case: (vertical_intersection_point _ _) => //).
Qed.

Lemma outgoing_high_opening s p g le he:
   valid_edge le p -> valid_edge he p ->
   {in s, forall g', left_pt g' == p} ->
   g \in s ->
   exists c, c \in opening_cells p s le he /\ high c = g.
Proof.
move=> vle vhe lefts'.
have {lefts'} lefts : {in sort (@edge_below _) s, forall g', left_pt g' == p}.
  by move=> g' g'in; apply lefts'; move: g'in; rewrite mem_sort.
rewrite -(mem_sort (@edge_below _)) /opening_cells.
elim: (sort _ _) le vle lefts => [ // | g0 s' Ih] le vle lefts.
rewrite inE=> /orP[/eqP <- /= |].
  rewrite (pvertE vle).
  case oca_eq : (opening_cells_aux _ _ _ _) => [so co] /=.
  eapply ex_intro; rewrite inE; split. 
    apply/orP; left; apply/eqP; reflexivity.
  by [].
move=> gin.
have vg : valid_edge g0 p.
  have := (@valid_edge_extremities _ g0 p).
  rewrite lefts ?eqxx //=; last by rewrite inE eqxx.
  by apply.
have lefts' : {in s', forall g', left_pt g' == p}.
  by move=> g' g'in; apply: lefts; rewrite inE g'in orbT.
have [c [cin cP]] := Ih _ vg lefts' gin.
exists c; rewrite /=. 
case oca_eq : (opening_cells_aux _ _ _ _) cin => [so co] /= cin.
by rewrite (pvertE vle) /= inE cin orbT cP.
Qed.

Lemma step_keeps_left_pt_open_lex e future_events open closed open2 closed2 :
  sorted (@lexPtEv _) (e :: future_events) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  s_right_form open ->
  out_left_event e ->
  step e open closed = (open2, closed2) ->
  {in open & (e :: future_events), forall c e',
     lexPt (left_pt (high c)) (point e')} ->
  {in open2 & future_events, forall c e',
     lexPt (left_pt (high c)) (point e')}.
Proof.
move=> sevs cbtom adj inbox_e sval rfo out_e; rewrite /step.
case oe : open_cells_decomposition => [[[[fc cc] lc] le] he].
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
move=> [<- _] lexp c e' + e'in.
have e'in2 : e' \in e :: future_events by rewrite inE e'in orbT.
rewrite !mem_cat orbCA=> /orP[]; last first.
  move=> cin; apply: lexp; last by [].
  by rewrite ocd !mem_cat orbCA cin orbT.
have vle : valid_edge le (point e).
  rewrite -leq; apply/(seq_valid_low sval)/map_f.
  by rewrite ocd ccq !mem_cat !inE eqxx !orbT.
have vhe : valid_edge he (point e).
  rewrite -heq; apply/(seq_valid_high sval)/map_f.
  by rewrite ocd ccq !mem_cat heceq mem_last !orbT.
move=> cino.
have := opening_cells_subset vle vhe out_e cino => /andP[] _.
rewrite inE => /orP[/eqP -> | ].
  rewrite -heq; apply: lexp; last by [].
  by rewrite ocd ccq !mem_cat heceq mem_last orbT.
move=> /out_e/eqP ->.
move: (sevs); rewrite /= (path_sortedE (@lexPtEv_trans _))=> /andP[] /allP + _.
by apply.
Qed.

Lemma step_keeps_open_cell_side_limit ev open closed open' closed' :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point ev) ->
  seq_valid open (point ev) ->
  out_left_event ev ->
  s_right_form open ->
  {in cell_edges open ++ outgoing ev &, no_crossing R} ->
  step ev open closed = (open', closed') ->
  all open_cell_side_limit_ok open ->
  all open_cell_side_limit_ok open'.
Proof.
move=> cbtom adj inbox_e sval out_e rfo nocs + allok; rewrite /step.
case oe : open_cells_decomposition => [[[[fc cc] lc] le] he] [] <- _.
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
apply/allP; move=> g; rewrite !mem_cat orbCA=> /orP[ | gold]; last first.
  by apply: (allP allok); rewrite ocd !mem_cat orbCA gold orbT.
move: g; apply/allP.
have [vl vh] := l_h_valid cbtom adj inbox_e sval oe.
have llh : le <| he.
  apply: open_cells_decomposition_low_under_high oe => //.
  by move=> g1 g2 g1in g2in; apply: nocs; rewrite mem_cat ?g1in ?g2in.
have [pale puhe] : point ev >>> le /\ point ev <<< he.
  by apply: l_h_above_under_strict oe.
apply: opening_cells_side_limit => //.
  by apply: underWC.
have lho_sub : {subset [::le, he & outgoing ev] <=
    cell_edges open ++ outgoing ev}.
  move=> g; rewrite 2!inE mem_cat => /orP[/eqP -> | /orP[/eqP -> | -> ]];
    last by rewrite orbT.
    by rewrite ocd mem_cat -leq map_f // ccq !mem_cat inE eqxx !orbT.
  by rewrite ocd mem_cat -heq map_f ?orbT // ccq !mem_cat heceq mem_last !orbT.
by move=> g1 g2 g1in g2in; apply: nocs; apply: lho_sub.
Qed.

Lemma step_keeps_edge_covering e open closed open2 closed2 :
(*  {in open, forall c, lexPt (left_pt (high c)) (point e)} -> *)
  all open_cell_side_limit_ok open ->
  bottom_left_cells_lex open (point e) ->
  open_non_inner_event open e ->
  {in open &, injective (@high R)} ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  s_right_form open ->
  out_left_event e ->
  forall g,
  edge_covered g open closed \/ g \in outgoing e ->
  step e open closed = (open2, closed2) ->
  edge_covered g open2 closed2.
Proof.
move=> (* lexleft *) opok btm_left
   n_inner ihigh cbtom adj inbox_e sval rfo out_e g; rewrite /step.
case oe : open_cells_decomposition => [[[[fc cc] lc] le] he].
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
have hdcclo : low (head_cell cc) = le by rewrite ccq.
have lcchi : high (last_cell cc) = he by rewrite ccq /last_cell /= -heceq.
move=> ecgVgo [] <- <- {open2 closed2}.
set new_cells := (X in fc ++ X ++ _).
set new_closed_cells := closing_cells _ _.
set open2 := (X in edge_covered _ X _).
set closed2 := (X in edge_covered _ _ X).
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have adjcc : adjacent_cells cc.
  by move: adj; rewrite ocd => /adjacent_catW [] _ /adjacent_catW[].
have svalcc : seq_valid cc (point e).
  apply/allP=> c' c'in; apply: (allP sval); rewrite ocd !mem_cat c'in.
  by rewrite orbT.
have [lu ha] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have cont := open_cells_decomposition_contains oe.
have vlhec : valid_edge (low hec) (point e).
  have hecincc : hec \in cc by rewrite ccq heceq mem_last.
  by apply/(seq_valid_low sval)/map_f; rewrite ocd !mem_cat hecincc !orbT.
have [/eqP ghe | gnhe] := boolP(g == he).
  have gno : g \notin outgoing e.
    apply/negP=> /(out_left_event_on out_e) abs.
    have [ _ ] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
    by rewrite strict_nonAunder // -ghe abs.
  case: ecgVgo; last by rewrite (negbTE gno).
  move=> [ | [pcc [A B]]]; last first.
    right; exists pcc; split;[ | exact B].
    by rewrite /closed2; move=> g1 /A; rewrite mem_cat => ->.
  move=> [hec1 [pcc1 [subp1 [ph [cl [oo ll]]]]]].
  have hec1q : hec1 = hec.
    apply: ihigh=> //.
      by rewrite ocd !mem_cat heceq ccq mem_last !orbT.
    by rewrite heq ph // mem_rcons inE eqxx.
  left; exists (last_cell new_cells), (rcons pcc1 (last_cell new_closed_cells)).
  split.
    move=> c; rewrite /closed2 !(mem_rcons, mem_cat, inE).
    move=> /orP[/eqP -> | /subp1 -> //].
    apply/orP; right.
    by rewrite /new_closed_cells/closing_cells ccq /last_cell /= mem_last.
  split.
    move=> c; rewrite !(mem_rcons, inE) => /orP[/eqP |/orP[/eqP | inpcc1]];
        last by apply: ph; rewrite mem_rcons inE inpcc1 orbT.
      move=> ->; rewrite ghe.
      by apply/eqP; apply: (higher_edge_new_cells out_e erefl vle vhe).
    rewrite /new_closed_cells/closing_cells/last_cell ccq /= => ->.
    rewrite last_map -heceq /close_cell.
    by rewrite (pvertE vlhec) heq (pvertE vhe) /= ghe.
  split.
(* I don't know if this is used later. *)
(*
      have last_conn : right_limit (last_cell new_closed_cells) =
                 left_limit (last_cell new_cells).
        rewrite /new_closed_cells/closing_cells/last_cell ccq.
        rewrite /= last_map -heceq /close_cell.
        rewrite (pvertE vlhec) heq (pvertE vhe) /=.
        set rl := right_limit _.
        have -> : rl = p_x (point e) by rewrite /rl; case: ifP; case: ifP=> //.
        apply/esym => {rl}.
        apply: (@opening_cells_left _ (outgoing e) le he).
        move: (opening_cells_not_nil (outgoing e) le he).
        rewrite -/new_cells.
        by case: (new_cells) => [ | a l ]; rewrite //= mem_last.
*)
(* End of fragment with unknown usage*)
    elim/last_ind : {-1} pcc1 (erefl pcc1) => [pcc1eq | pcc1' lpcc1 _ pcc1eq].
      rewrite /new_closed_cells/closing_cells/last_cell ccq /= last_map.
      rewrite /close_cell.
      set rl := right_limit _.
      have -> : rl = p_x (point e).
        rewrite /rl -heceq (pvertE vlhec) heq (pvertE vhe) /=.
        by case: ifP => [latpointe | lnotpointe];
           case: ifP => [hatpointe | hnotpointe].
      rewrite eq_sym andbT; apply/eqP.
      apply: (opening_cells_left out_e vle vhe).
      by apply/last_in_not_nil/opening_cells_not_nil.
    rewrite -pcc1eq connect_limits_rcons; last by apply/eqP/rcons_neq0.
    apply/andP; split; last first.
      rewrite last_rcons /new_closed_cells/closing_cells ccq [map _ _]/=.
      rewrite /last_cell /= last_map.
      rewrite right_limit_close_cell -?heceq // ?heq //.
      rewrite (@opening_cells_left (point e) (outgoing e) le he) //.
      by apply/last_in_not_nil/opening_cells_not_nil.
    rewrite /new_closed_cells/closing_cells ccq /last_cell /= last_map -heceq.
    move: cl; rewrite hec1q pcc1eq connect_limits_rcons; last first.
      by apply/eqP/rcons_neq0.
    rewrite (@connect_limits_rcons R (rcons _ _)); last first.
      by apply/eqP/rcons_neq0.
    move=> /andP[] -> /= /eqP ->.
    by rewrite left_limit_close_cell eqxx.
  split.
    rewrite /open2 !mem_cat last_in_not_nil ?orbT //.
    by apply: opening_cells_not_nil.
  move: ll.
  case pcc1q: pcc1 => [ | pcc0 pcc1']; last by [].
  rewrite /head_cell/new_closed_cells/closing_cells/last_cell ccq /=.
  by rewrite last_map -heceq left_limit_close_cell hec1q.
case: ecgVgo=> [ecg |go ]; last first.
  left.
  case: (outgoing_high_opening vle vhe out_e go) => [c [cin cP]].
  exists c, [::]; rewrite /=; split.
    by move=> x xin.
  split; first by move=> c'; rewrite inE => /eqP->.
  split; first by [].
  split; first by rewrite /open2 /new_cells !mem_cat cin ?orbT.
  rewrite (opening_cells_left out_e vle vhe cin); apply/esym/eqP.
  by rewrite (eqP (out_e g go)) eqxx.
case: ecg => [| [pcc [subcl All_other]]]; last first.
  right; exists pcc; split;[ | exact All_other].
  by move=> c cin; rewrite /closed2 mem_cat subcl.
move=> [opc [pcc [subcl [highs [conn [/[dup] opcopen + leftl]]]]]].
rewrite ocd; rewrite !mem_cat orbCA => /orP[]; last first.
  move=> inO.
  left; exists opc, pcc.
  split; first by move=> c cin; rewrite /closed2 mem_cat subcl.
  split; first by [].
  split; first by [].
  split; first by rewrite /open2 /new_cells !mem_cat orbCA inO orbT.
  by [].
move=> opcc.
right.
have [_ highopc leftopc]:= close_cell_preserve_3sides (point e) opc.
exists (rcons pcc (close_cell (point e) opc)).
split.
  move=> c; rewrite mem_rcons inE=> /orP[/eqP -> | ].
    rewrite /closed2 mem_cat/new_closed_cells/closing_cells; apply/orP; right.
    by apply/mapP; exists opc.
  by move=> cin; rewrite /closed2 mem_cat subcl.
split.
  move=> c; rewrite mem_rcons inE => /orP[/eqP -> | inpcc]; last first.
    by apply highs; rewrite mem_rcons inE inpcc orbT.
  by rewrite highopc; apply highs; rewrite mem_rcons inE eqxx.
split.
  have [/eqP -> | pccn0] := boolP (pcc == [::]).
    by [].
  move: conn; rewrite !connect_limits_rcons // => /andP[] -> /eqP -> /=.
  by rewrite /left_limit leftopc.
split.
  move: leftl; case pccq: pcc => [ | pcc0 pcc'] //=.
  by rewrite /left_limit leftopc.
rewrite /last_cell last_rcons right_limit_close_cell; last first.
    by apply/(seq_valid_high sval)/map_f.
  by apply/(seq_valid_low sval)/map_f.
have hopc : high opc = g by apply: highs; rewrite mem_rcons inE eqxx.
have e_on : point e === high opc.
  apply: (open_cells_decomposition_point_on cbtom adj inbox_e sval oe opcc).
  by rewrite hopc.
have [ abs | -> ] := n_inner _ opcopen e_on; last by rewrite hopc.
have := bottom_left_lex_to_high cbtom adj rfo opok inbox_e btm_left opcopen.
by rewrite abs lexPt_irrefl.
Qed.

Lemma step_keeps_subset open closed open' closed' ev :
  cells_bottom_top open ->
  adjacent_cells open ->
  seq_valid open (point ev) ->
  out_left_event ev ->
  inside_box (point ev) ->
  step ev open closed = (open', closed') ->
  {subset cell_edges open' <= cell_edges open ++ outgoing ev}.
Proof.
move=> cbtom adj sval out_e inbox_e.
rewrite /step.
case oe : (open_cells_decomposition open (point ev)) =>
  [[[[fc cc] lc] le] he] [] <- _.
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
have vle : valid_edge le (point ev).
  rewrite -leq; apply/(seq_valid_low sval)/map_f.
  by rewrite ocd ccq !mem_cat !inE eqxx !orbT.
have vhe : valid_edge he (point ev).
  rewrite -heq; apply/(seq_valid_high sval)/map_f.
  by rewrite ocd ccq !mem_cat heceq mem_last !orbT.
move=> g; rewrite ocd !cell_edges_cat mem_cat cell_edges_cat.
rewrite  [X in _ || X]mem_cat orbCA=> /orP[ | gold]; last first.
  rewrite /all_edges mem_cat cell_edges_cat mem_cat cell_edges_cat.
  by rewrite [X in _ || X || _]mem_cat orbCA gold !orbT.
rewrite mem_cat=> /orP[] /mapP [] c cin gq.
  have gle_or_out : g = le \/ g \in outgoing ev.
    have:= opening_cells_subset vle vhe out_e cin.
    rewrite -gq inE=> /andP[]/orP[/eqP| ] ->;
    by auto.
  move: gle_or_out => [-> | ].
    by rewrite !mem_cat ccq -leq map_f // !mem_cat inE eqxx !orbT.
  by rewrite /all_edges mem_cat orbC /events_to_edges /= mem_cat=> ->.
have ghe_or_out : g = he \/ g \in outgoing ev.
  have:= opening_cells_subset vle vhe out_e cin.
   by rewrite -gq andbC inE=> /andP[]/orP[/eqP|]->; auto.
move: ghe_or_out => [-> | ].
  rewrite !mem_cat ccq -heq map_f ?orbT //.
  by rewrite heceq !mem_cat mem_last !orbT.
by rewrite /all_edges mem_cat orbC /events_to_edges /= mem_cat=> ->.
Qed.

Lemma above_point_in_closing open p q fc cc lc le he:
   cells_bottom_top open -> adjacent_cells open -> inside_box p ->
   seq_valid open p -> s_right_form open ->
   {in open, forall c, left_limit c <= p_x p} ->
   open_cells_decomposition open p = (fc , cc, lc, le, he) ->
   p_x q = p_x p -> p_y p < p_y q -> q <<= he ->
   inside_closed' q (last dummy_cell (closing_cells p cc)) ||
   ~~has (inside_open' q) open.
Proof.
move=> cbtom adj inbox_p sval rfo llim oe samex above under.
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_p oe.
have adjcc : adjacent_cells (lec :: cc').
  by move: adj; rewrite ocd ccq=> /adjacent_catW[] _ /adjacent_catW[] + _.
have valcc : seq_valid (lec :: cc') p.
  by apply/allP=> x xin; apply: (allP sval); rewrite ocd !mem_cat ccq xin !orbT.
have vhe : valid_edge he p.
  by apply: (seq_valid_high valcc); rewrite -heq map_f // heceq mem_last.
have vhep : valid_edge (high hec) p by rewrite heq.
have /allP cont := open_cells_decomposition_contains oe.
rewrite ccq in cont.
have [pal puh] := l_h_above_under_strict cbtom adj inbox_p sval rfo oe.
rewrite ccq closing_cells_single_map.
have vlep : valid_edge (low hec) p.
  apply: (seq_valid_low sval); rewrite ocd ccq; apply: map_f.
  by rewrite !mem_cat heceq mem_last orbT.
have trp : forall g, valid_edge g p -> valid_edge g q.
  by move=> g; rewrite /valid_edge samex.
rewrite inside_closed'E /= last_map -heceq.
rewrite left_limit_close_cell right_limit_close_cell //.
have : left_limit hec <= p_x q.
  by rewrite samex; apply: llim; rewrite ocd ccq heceq !mem_cat mem_last orbT.
have vle : valid_edge le p.
  by apply: (seq_valid_low valcc); rewrite -leq map_f // inE eqxx.
have vleq : valid_edge le q by apply/trp.
have samex' : p_x q == p_x p by apply/eqP.
have samex'' : p_x p == p_x q by apply/eqP.
have vlhq : valid_edge (low hec) q by apply/trp.
have qal : q >>> low hec.
  have [/eqP cc'0 | cc'n0] := boolP(cc' == [::]).
    rewrite heceq cc'0 /= leq under_pvert_y // -ltNge (lt_trans _ above) //.
    rewrite (eqP (same_pvert_y vleq samex')).
    by move: pal; rewrite under_pvert_y // -ltNge.
  have /andP[+ _] : contains_point p hec.
    by apply: (allP cont); rewrite heceq mem_last.
  rewrite strict_under_pvert_y // -leNgt.
  rewrite -(eqP (same_pvert_y vlhq samex'))=> /le_lt_trans /(_ above).
  by rewrite ltNge -under_pvert_y.
rewrite le_eqVlt=> /orP[/eqP hec0 | ->]; last first.
  rewrite samex le_refl /close_cell (pvertE vhep) (pvertE vlep) /=.
  by rewrite heq under qal.
apply/orP; right; apply/negP=> /hasP[c /[dup] cin + qinc].
have vcp : valid_edge (low c) p /\ valid_edge (high c) p.
  by apply/andP; apply: (allP sval).
have [vlq vhq] : valid_edge (low c) q /\ valid_edge (high c) q.
  by move: vcp=> [] /trp + /trp.
move: vcp=> [vlp vhp].
have hdo : head dummy_edge [seq low i | i <- open] = bottom.
    by move: cbtom => /andP[]; case: (open)=> [ // | a l] /= /eqP ->.
have := seq_edge_below' adj rfo; rewrite hdo ocd !map_cat !cat_path => patheb.
rewrite !mem_cat orbCA => /orP[cincc | cold]; last first.
  move: cold=> /orP[] /[dup] cold /mem_seq_split [s1 [s2 s1s2q]].
    have := decomposition_above_high_fc oe cbtom adj inbox_p rfo sval cold.
    rewrite under_pvert_y // -ltNge.
    move: qinc; rewrite inside_open'E => /andP[] + _.
    rewrite under_pvert_y //; rewrite -(eqP (same_pvert_y vhp _)) //.
    move=> /le_lt_trans it; move=> {}/it /(lt_trans above).
    by rewrite lt_irreflexive.
  have : all (fun g => valid_edge g p) (he :: [seq high i | i <- lc]).
    rewrite /= -heq (seq_valid_high valcc) ?andTb; last first.
      by rewrite map_f // heceq mem_last.
    apply/allP=> x /mapP [xc xcin xeq]; apply: (seq_valid_high sval).
    by apply/mapP; exists xc=> //; rewrite ocd !mem_cat xcin !orbT.
  move=> /path_edge_below_pvert_y convert.
  move:(patheb)=> /andP[] _ /andP[] _; rewrite ccq /= last_map -heceq heq.
  move=> {}/convert; rewrite le_path_sortedE => /andP[] abovehe _.
  move: adj; rewrite ocd ccq=> /adjacent_catW [] _ /=.
  rewrite cat_path => /andP[] _; rewrite s1s2q cat_path => /andP[] _ /= /andP[].
  move=> /eqP/esym lcq _.
  move: qinc; rewrite inside_open'E => /andP[] _ /andP[] + _.
  rewrite under_pvert_y // lcq.
  have vheq : valid_edge he q by apply: trp.
  case s1q : s1 => [ | c0 s1'].
    by rewrite /= -heceq heq -under_pvert_y ?under.
  have vlp' : valid_edge (high (last c0 s1')) p.
    by move: lcq; rewrite s1q /= => <-.
  rewrite /= -ltNge -(eqP (same_pvert_y vlp' _))=> [ql | ]; last first.
    by apply/eqP.
  have : last c0 s1' \in lc by rewrite s1s2q s1q mem_cat mem_last.
  move=> /(map_f (@high R)) /(map_f (pvert_y p)) m.
  have hel := (allP abovehe _ m).
  move: under; rewrite under_pvert_y // leNgt -(eqP (same_pvert_y vhe _)) //.
  by rewrite (le_lt_trans hel ql).
have cnhec : c <> hec.
  by move: qinc=> /[swap] ->; rewrite inside_open'E hec0 lt_irreflexive ?andbF.
have [cc1 cc1p] : exists cc1, cc = cc1 ++ [:: hec].
  elim/last_ind: (cc) ccq => [// | cc1 b _] it.
  exists cc1; rewrite cats1 heceq; congr (rcons _ _).
  by rewrite -[b](last_rcons b cc1) it.
move: cincc; rewrite cc1p mem_cat inE=> /orP[ | /eqP abs]; last by case: cnhec.
move=> /mem_seq_split [s1 [s2 s1s2q]].
have /path_edge_below_pvert_y convert : all (fun g => valid_edge g p)
   (last bottom [seq high i | i <- fc] :: [seq high i | i <- cc]).
    rewrite /=; apply/andP; split; last first.
    by apply/allP=> x xin; apply: (seq_valid_high valcc); rewrite -ccq.
  case fcq : fc => [/= | c0 fc1].
    by apply: (inside_box_valid_bottom_top inbox_p)=> //; rewrite inE eqxx.
  rewrite /= last_map; apply: (seq_valid_high sval).
  by rewrite ocd fcq map_cat mem_cat map_f // mem_last.
move: patheb => /andP[] _ /andP[] /convert +  _.
rewrite cc1p s1s2q -catA /= !map_cat cat_path=> /andP[] _ /= /andP[] _.
rewrite le_path_sortedE=> /andP[] cmpchec _.
move: (adjcc); rewrite -ccq cc1p s1s2q -catA=> /adjacent_catW[] _ /=.
rewrite cat_path=>/andP[] _ ls2.
have cmp' : pvert_y p (high c) <= pvert_y p (low hec).
  case s2q : s2 => [ | c1 s2'].
    by move: ls2; rewrite s2q /= andbT => /eqP ->.
  have tin : pvert_y p (high (last c1 s2')) \in
             [seq pvert_y p g | g <- [seq high i | i <- s2 ++ [:: hec]]].
    by rewrite map_f // map_f // mem_cat s2q mem_last.
  move: (allP cmpchec _ tin).
  by move: ls2; rewrite s2q /= andbT=> /eqP ->.
move: qinc; rewrite inside_open'E=> /andP[] + _ .
rewrite under_pvert_y // -(eqP (same_pvert_y vhp _)) // => cmp2.
have := le_trans cmp2 cmp'.
move: qal; rewrite under_pvert_y // -(eqP (same_pvert_y vlep _)) //.
by move=> /negbTE ->.
Qed.

Lemma step_keeps_cover_left_border e open closed open' closed' evs :
  (*sorted (@lexPt R) [seq point x | x <- (e :: evs)] -> *)
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  out_left_event e ->
  s_right_form open ->
  close_alive_edges open (e :: evs) ->
  close_edges_from_events (e :: evs) ->
  {in cell_edges open ++ flatten [seq outgoing i | i <- e :: evs] &,
     no_crossing R} ->
  bottom_left_cells_lex open (point e) ->
  step e open closed = (open', closed') ->
  {in open, forall c p, inside_box p -> left_limit c = p_x p ->
    contains_point' p c -> has (inside_closed' p) closed} ->
  {in open', forall c p, inside_box p -> left_limit c = p_x p ->
    contains_point' p c -> has (inside_closed' p) closed'}.
Proof.
move=> (*sortevs*) cbtom adj inbox_e sval oute rfo clae clev noc btm_left stepeq.
have := step_keeps_bottom_top inbox_e sval adj cbtom oute stepeq.
have := step_keeps_adjacent inbox_e oute sval cbtom stepeq adj.
have := step_keeps_left_pts_inf' inbox_e oute rfo sval adj cbtom clae
  clev noc btm_left stepeq.
have := step_keeps_closeness inbox_e oute rfo cbtom adj sval clev clae
   stepeq.
have :=
   step_keeps_valid _ inbox_e _ oute rfo cbtom adj sval clae clev _ stepeq.
have noc' : {in cell_edges open ++ outgoing e &, no_crossing R}.
  by move=> g1 g2 g1in g2in; apply: noc; rewrite /= !mem_cat orbA
   -2!mem_cat ?g1in ?g2in.
have rfo' := step_keeps_right_form cbtom adj inbox_e sval noc' oute rfo stepeq.
move: stepeq; rewrite /step /=.
case oe : (open_cells_decomposition open (point e)) => [[[[fc cc] lc] le] he].
move=> [] /esym openeq /esym closeeq.
move=> sval0' clae' btm_left' adj' cbtom' left_border c cin p inboxp lbnd pin.
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
    lhc_dec cbtom adj inbox_e oe.
move: cin; rewrite openeq !mem_cat orbCA orbC=> /orP[cold | cnew].
  rewrite closeeq has_cat; apply/orP; left.
  apply: (left_border c _ _ inboxp lbnd pin).
  by rewrite ocd !mem_cat orbCA cold orbT.
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have ppe : p_x p = p_x (point e).
  by rewrite -lbnd (opening_cells_left oute vle vhe cnew).
have adjcc : adjacent_cells cc.
  by move: adj; rewrite ocd=> /adjacent_catW[] _ /adjacent_catW[].
have valcc : seq_valid cc (point e).
  by apply/allP=> x xin; apply: (allP sval); rewrite ocd !mem_cat xin ?orbT.
have [ea eu] : point e >>> low (head dummy_cell cc) /\
          point e <<< high (last dummy_cell cc).
  rewrite ccq /= leq -heceq heq.
  apply: (l_h_above_under_strict cbtom adj inbox_e sval rfo oe).
have allcont : all (contains_point (point e)) cc.
  by apply/allP=> x xin; apply: (open_cells_decomposition_contains oe).
have /andP [vlep vhep] : valid_edge le p && valid_edge he p.
  by move: vle vhe; rewrite /valid_edge ppe=> -> ->.
have lonew : low (head dummy_cell
                 (opening_cells (point e) (outgoing e) le he)) = le.
  by have := lower_edge_new_cells vle vhe erefl vle vhe => /eqP.
have lonew' : head dummy_edge
    [seq low c | c <- opening_cells (point e) (outgoing e) le he] = le.
  move: (opening_cells_not_nil (outgoing e) le he) lonew.
  by set w := opening_cells _ _ _ _; case: w=> [ | a tl].
have highnew : [seq high i | i <- opening_cells (point e)(outgoing e) le he]=
               rcons (sort (@edge_below _) (outgoing e)) he.
  by rewrite (opening_cells_high vle vhe).
have allval : all (fun g => valid_edge g p) 
     (head dummy_edge [seq low i | i <- opening_cells (point e) 
              (outgoing e) le he] ::
     [seq high i | i <- opening_cells (point e) (outgoing e) le he]).
  apply/allP=> x; rewrite inE=> xin.
  suff : valid_edge x (point e) by rewrite /valid_edge ppe.
  move: xin=> /orP[/eqP xin | xin]; first by rewrite xin lonew'.
  rewrite (opening_cells_high vle vhe) // ?mem_rcons inE mem_sort in xin.
  case/orP: xin=> [/eqP -> // | xin ].
  apply: valid_edge_extremities; apply/orP; left.
  by apply: oute.
have lecc : lec \in cc by rewrite ccq inE eqxx.
have lecin : lec \in open.
  by rewrite ocd !mem_cat lecc orbT.
have vhlece : valid_edge (high lec) (point e).
  by have := seq_valid_high sval (map_f (@high R) lecin).
have vhlecp : valid_edge (high lec) p.
  by move: vhlece; rewrite /valid_edge ppe.        
move: adj'; rewrite openeq=> /adjacent_catW[] _ /adjacent_catW[] adjo _.
have [yle | yabove] := lerP (p_y p) (p_y (point e)).
  have pale : p >>> le.
    have /mem_seq_split [s1 [s2 s1s2q]] := cnew.
    case s1q : s1 => [ | c0 s1'].
      by move: lonew; rewrite s1s2q s1q /= => <-; move: pin=> /andP[].
    have lco : low c \in outgoing e.
      have := seq_low_high_shift
                (opening_cells_not_nil (outgoing e) le he (point e))
                adjo.
      rewrite s1s2q s1q /= => - [].
      rewrite -[RHS]/[seq high i | i <- (c0 :: s1') ++ c :: s2] -s1q -s1s2q.
      rewrite opening_cells_high // => /rcons_inj [] lows _.
      have : low c \in [seq low i | i <- s1' ++ c :: s2].
        by apply: map_f; rewrite mem_cat inE eqxx orbT.
      by rewrite lows mem_sort.
    have vlce : valid_edge (low c) (point e).
      by apply: valid_edge_extremities; rewrite (oute (low c)).
    move: pin => /andP[] + _; rewrite under_pvert_y; last first.
      by move: vlce; rewrite /valid_edge ppe.
    rewrite -(eqP (same_pvert_y vlce _)); last by apply/eqP.
    by rewrite on_pvert ?yle // -(eqP (oute (low c) _)) // left_on_edge.
  have plec : contains_point' p lec.
    rewrite /contains_point' leq pale /=.
    rewrite under_pvert_y  //.
    apply: (le_trans yle); rewrite -(eqP (same_pvert_y vhlece _)); last first.
      by apply/eqP.
    rewrite -under_pvert_y //.
    have/(open_cells_decomposition_contains oe)/andP[]// : lec \in cc.
    by rewrite ccq inE eqxx.
  have [/eqP lbnd' | safe] := boolP(left_limit lec == p_x p).
    rewrite closeeq has_cat.
    by rewrite (left_border _ lecin).
  have lbnd2 : left_limit lec < p_x p.
    rewrite lt_neqAle safe /=.
    rewrite ppe; apply/lexePt_xW/lexPtW.
    by apply: (btm_left lec lecin).
  rewrite closeeq has_cat; apply/orP; right.
  apply/hasP; exists (close_cell (point e) lec).
    by apply:map_f; rewrite ccq inE eqxx.
  have vlec : valid_cell lec (point e).
    by apply/andP; apply: (allP valcc); rewrite ccq inE eqxx.
  rewrite inside_closed'E /left_limit.
  have [-> -> ->]:= close_cell_preserve_3sides (point e) lec.
  move: plec=> /andP[] -> ->.
  by rewrite (close_cell_right_limit) // lbnd2 ppe lexx.
have phec : contains_point' p hec.
  have puhe : p <<= he.
    have /mem_seq_split [s1 [s2 s1s2q]] := cnew.
    elim /last_ind: {2} (s2) (erefl s2) => [ | s2' c2 _] s2q.
      move: highnew; rewrite s1s2q s2q /= map_cat /= cats1=> /rcons_inj[] _ <-.
      by move: pin => /andP[].
    have hco : high c \in outgoing e.
      have := opening_cells_high vle vhe oute; rewrite s1s2q s2q.
      rewrite (_ : [seq high i | i <- s1 ++ c :: rcons s2' c2] =
             rcons [seq high i | i <- s1 ++ c :: s2'] (high c2)); last first.
        by rewrite !map_cat /= map_rcons -!cats1 /= -!catA /=.
      move=> /rcons_inj[] his _.
      have : high c \in [seq high i | i <- s1 ++ c :: s2'].
        by apply: map_f; rewrite mem_cat inE eqxx orbT.
      by rewrite his mem_sort.
    have vhce : valid_edge (high c) (point e).
      by apply: valid_edge_extremities; rewrite (oute (high c)).
    move: (pin) => /andP[] _; rewrite under_pvert_y; last first.
      by move: vhce; rewrite /valid_edge ppe.
    rewrite -(eqP (same_pvert_y vhce _)); last by apply/eqP.
    rewrite on_pvert; last first.
      by rewrite -(eqP (oute (high c) _)) // left_on_edge.
    move=> ple.
    have ppe': p_y p = p_y (point e).
      by apply: le_anti; rewrite ple (ltW yabove).
    have/eqP -> : p == point e by rewrite pt_eqE ppe ppe' !eqxx.
    by apply/underW; move: eu; rewrite ccq /= -heceq heq.
  rewrite /contains_point'; rewrite heq puhe andbT.
  have vlhece : valid_edge (low hec) (point e).
    apply: (seq_valid_low valcc); apply/map_f.
    by rewrite ccq heceq mem_last.
  have vlhecp : valid_edge (low hec) p.
    by move: vlhece; rewrite /valid_edge ppe.
  rewrite under_pvert_y // -?ltNge.
  apply: le_lt_trans yabove.  
  rewrite -(eqP (same_pvert_y vlhece _)); last by apply/eqP.
  rewrite leNgt -strict_under_pvert_y //.
  have/(open_cells_decomposition_contains oe)/andP[]// : hec \in cc.
    by rewrite ccq heceq mem_last.
have hecin : hec \in open.
    by rewrite ocd ccq !mem_cat heceq mem_last !orbT.
have [/eqP lbnd' | safe] := boolP(left_limit hec == p_x p).
  rewrite closeeq has_cat.
  by have -> := left_border _ hecin _ _ lbnd' phec.
have lbnd2 : left_limit hec < p_x p.
  rewrite lt_neqAle safe /=.
  rewrite ppe; apply/lexePt_xW/lexPtW.
  by apply: (btm_left hec hecin).
rewrite closeeq has_cat; apply/orP; right.
apply/hasP; exists (close_cell (point e) hec).
  by apply: map_f; rewrite ccq heceq mem_last.
have vhec : valid_cell hec (point e).
  by apply/andP; apply: (allP valcc); rewrite ccq heceq mem_last.
rewrite inside_closed'E /left_limit.
have [-> -> ->]:= close_cell_preserve_3sides (point e) hec.
move: phec=> /andP[] -> ->.
by rewrite (close_cell_right_limit) // lbnd2 ppe lexx.
Qed.

Lemma step_keeps_cover e open closed open' closed' p evs :
  sorted (@lexPt R) [seq point x | x <- (e :: evs)] ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  out_left_event e ->
  s_right_form open ->
  close_alive_edges open (e :: evs) ->
  close_edges_from_events (e :: evs) ->
  {in cell_edges open ++ flatten [seq outgoing i | i <- e :: evs] &,
     no_crossing R} ->
  bottom_left_cells_lex open (point e) ->
  {in open, forall c p, inside_box p -> left_limit c = p_x p ->
    contains_point' p c -> has (inside_closed' p) closed} ->
  step e open closed = (open', closed') ->
  cover_left_of (point e) open closed ->
  all (lexePt p) [seq point e | e <- evs] ->
  cover_left_of p open' closed'.
Proof.
move=> sortevs cbtom adj inbox_e sval oute rfo clae clev noc btm_left 
  left_border_in stepeq.
have cbtom' := step_keeps_bottom_top inbox_e sval adj cbtom oute stepeq.
have adj' := step_keeps_adjacent inbox_e oute sval cbtom stepeq adj.
have := step_keeps_left_pts_inf' inbox_e oute rfo sval adj cbtom clae
  clev noc btm_left stepeq.
have := step_keeps_closeness inbox_e oute rfo cbtom adj sval clev clae
   stepeq.
have :=
   step_keeps_valid _ inbox_e _ oute rfo cbtom adj sval clae clev _ stepeq.
have := step_keeps_cover_left_border cbtom adj inbox_e sval oute rfo clae clev
  noc btm_left stepeq left_border_in.
move: stepeq; rewrite /step /=.
case oe : (open_cells_decomposition open (point e)) => [[[[fc cc] lc] le] he].
have subcc : {subset cc <= open}.
  by move=> x xin; rewrite (decomposition_preserve_cells oe) !mem_cat xin orbT.
move=> [] open'eq closed'eq left_border_in' 
  sval0' clae' btm_left' cov limr q inbox_q limrq.
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
   lhc_dec cbtom adj inbox_e oe.
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have [qright | qleft] := boolP(lexPt (point e) q).
  have [c cin ctn]:= exists_cell cbtom' adj' inbox_q.
  have subpq1 : subpred (lexePt p) (lexePt q).
    by move=> x px; apply/(lexePt_trans limrq).
  have limrq1 := sub_all subpq1 limr.
  have limrq' : forall e, e \in evs -> lexePt q (point e).
    by move/(sub_all subpq1): (limr); rewrite all_map=>/allP.
  have sval' := sval0' _ inbox_q qright limrq'.
  move: cin; rewrite -open'eq !mem_cat orbCA -mem_cat => /orP[] cin; last first.
    have [inc | ninc] := boolP(inside_open' q c).
      rewrite 2!has_cat orbCA -has_cat; apply/orP; left; apply/orP; right.
      by apply/hasP; exists c.
    have cin0 : c \in open by rewrite ocd !mem_cat orbCA -mem_cat cin ?orbT.
    have cin1 : c \in open'.
      by rewrite -open'eq !mem_cat orbCA -mem_cat cin orbT.
    apply/orP; right.
    rewrite -closed'eq has_cat; apply/orP; left.
    move: ninc; rewrite inside_open'E; rewrite lt_neqAle.
    move: (ctn)=> /andP[] -> -> /=.
    have -> : left_limit c <= p_x q.
      have : p_x (point e) <= p_x q by apply/lexePt_xW/lexPtW.
      apply: le_trans.
      rewrite /left_limit -[X in X <= _]/(p_x (bottom_left_corner c)).
      by apply/lexePt_xW/lexPtW; apply: btm_left.
    have -> : p_x q <= open_limit c.
      rewrite /open_limit le_minr.
      have extg : forall g, g \in [:: bottom; top] -> p_x q <= p_x (right_pt g).
        move: inbox_q=> /andP[] _ /andP[] /andP[] _ /ltW + /andP[] _ /ltW.
        by move=> A B g; rewrite !inE=> /orP[] /eqP ->.
      have intg g : has (event_close_edge g) evs -> p_x q <= p_x (right_pt g).
        move=>/hasP[] ev' ev'in /eqP ->.
        by apply/lexePt_xW/(lexePt_trans limrq)/(allP limr)/map_f.
      move: clae' => /allP /(_ _ cin1) /andP[].
      by move=> /orP[/extg | /intg] -> /orP[/extg | /intg] ->.
    rewrite !andbT negbK => /eqP atll.
    by apply: (left_border_in _ cin0 _ inbox_q atll ctn).
  have [vertp | rightofp] : left_limit c = p_x q \/ left_limit c < p_x q.
      rewrite (opening_cells_left oute vle vhe cin).
      move: qright=> /lexPtW/lexePt_xW; rewrite le_eqVlt=> /orP[/eqP -> | ->].
        by left.
      by right.
    rewrite (left_border_in' _ _ _ _ vertp ctn) ?orbT //.
    by rewrite -open'eq !mem_cat cin orbT.
  rewrite !has_cat; apply /orP; left; apply/orP; right; apply/orP; left.
  apply/hasP; exists c=> //.
  rewrite inside_open'E rightofp /open_limit le_minr.
  have [/andP[_ ->] /andP[_ ->]] : valid_cell c q.
    by apply/andP; apply: (allP sval'); rewrite -open'eq !mem_cat cin ?orbT.
  by move: ctn=> /andP[] -> ->.
have qe : p_x q <= p_x (point e).
  by apply: lexePt_xW; rewrite lexePtNgt.
have inclosing : forall c, c \in cc -> inside_open' q c ->
  (forall c, c \in cc -> valid_edge (low c) (point e) &&
     (valid_edge (high c) (point e))) ->
  exists2 c', c' \in closing_cells (point e) cc & inside_closed' q c'.
  move=> c cin ins allval.
  have /allP ctps : forall c, c \in cc -> contains_point (point e) c.
    by move=> ?; apply: (open_cells_decomposition_contains oe).
  have [/eqP/esym lel [/eqP/esym heh _]] :=
     l_h_c_decomposition oe (exists_cell cbtom adj (inbox_e)).
  have [eabovel ebelowh] :=
        l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  have ccsub : {subset cc <= open}.
    by move=> x xin; rewrite ocd !mem_cat xin orbT.
  exists (close_cell (point e) c).
    by apply: map_f.
  rewrite /inside_closed_cell.
  move: ins; rewrite inside_open'E andbA=>/andP[] ctn /andP[liml _] /=.
  move: ctn=>/andP [qlc qhc].
  rewrite /contains_point/close_cell /=.
  have [p1 vip1] := exists_point_valid (proj1 (andP (allval _ cin))).
  have [p2 vip2] := exists_point_valid (proj2 (andP (allval _ cin))).
  have [onl x1] := intersection_on_edge vip1.
  have [onh x2] := intersection_on_edge vip2.
  by rewrite inside_closed'E vip1 vip2 qlc qhc; case: ifP=> [p1e | p1ne];
    case: ifP=> [p2e | p2ne]; rewrite liml /right_limit /= -?x2 -?x1.
move: qleft; rewrite -lexePtNgt lexePt_eqVlt.
have svalcc :
   forall c : cell,
     c \in cc -> valid_edge (low c) (point e) && valid_edge (high c) (point e).
   by move=> x /subcc xin; apply: (allP sval).
move=> /orP[/eqP qe' | qlte ].
  rewrite qe'.
  apply/orP; right; apply/hasP.
  set opc := head dummy_cell cc.
  have opcin : opc \in cc by rewrite /opc ccq /= !inE eqxx.
  have opcin' : opc \in open by rewrite subcc.
  have adjcc : adjacent_cells cc.
    by move: adj; rewrite ocd => /adjacent_catW[] _ /adjacent_catW[].
  have [leftb | nleftb] :=
    boolP(p_x (last dummy_pt (left_pts opc)) < p_x (point e)); last first.
    have notinopen : {in open, forall c, ~~ inside_open' (point e) c}.
      move=> c; rewrite ocd !mem_cat orbCA => /orP[]; last first.
        rewrite inside_open'E; move=> cold; apply/negP=> inec; move: cold.
        move=> /(decomposition_not_contain rfo sval adj cbtom inbox_e oe)[].
        by rewrite /contains_point; move: inec=> /andP[] -> /andP[] /underWC ->.
      rewrite ccq inE=> /orP[/eqP -> | ].
        rewrite inside_open'E; apply/negP=> inlec; case/negP: nleftb.
        move: inlec=> /andP[] _ /andP[] _ /andP[] + _.
        by rewrite /left_limit /opc ccq.
      move/mem_seq_split=> [s1 [s2 cc'q]].
      have hls1q : high (last lec s1) = low c.
        move: adjcc; rewrite /adjacent_cells ccq cc'q /= cat_path=> /andP[] _.
        by rewrite /= => /andP[] /eqP.
      have llecin : last lec s1 \in cc.
        rewrite ccq cc'q -[_ :: _]/((lec :: s1)++ (c :: s2)).
        by rewrite mem_cat mem_last.
      have : point e <<= low c.
        have := open_cells_decomposition_contains oe llecin=> /andP[] _.
        by rewrite hls1q.
      by rewrite inside_open'E => ->; rewrite !andbF.
    move: (cov (point e) inbox_e (lexePt_refl _)) => /orP[] /hasP [x xin Px].
      by have := notinopen x xin; rewrite Px.
    by exists x => //; rewrite -closed'eq mem_cat xin.
  have : inside_open' (point e) opc.
    have elt : all (lexePt (point e)) [seq point e0 | e0 <- e :: evs].
      rewrite /=; rewrite lexePt_eqVlt eqxx /=.
      move: sortevs; rewrite /=; rewrite path_sortedE; last exact: lexPt_trans.
      by move=> /andP[+ _]; apply: sub_all; move=> y; apply: lexPtW.
    have : contains_point' (point e) opc.
      have := open_cells_decomposition_contains oe opcin.
      rewrite /contains_point'=> /andP[] _ ->.
      rewrite /opc ccq /= leq.
      by have [-> _] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
    by apply: (contains_to_inside_open' sval clae inbox_e leftb).
  rewrite -qe'=> einopc.
  have [it it1 it2]:= inclosing _ opcin einopc svalcc.
  by exists it=> //; rewrite -closed'eq mem_cat it1 orbT.
have := cov q inbox_q (lexPtW qlte)=> /orP[ | already_closed]; last first.
  by rewrite -closed'eq has_cat already_closed orbT.
rewrite -open'eq (decomposition_preserve_cells oe).
rewrite 2!has_cat orbCA=> /orP[/hasP [opc opcin qinopc] | keptopen].
  have [it it1 it2] := inclosing _ opcin qinopc svalcc.
  apply/orP; right; apply/hasP.
  by exists it=> //; rewrite -closed'eq mem_cat it1 orbT.
apply/orP; left; apply/hasP.
move: keptopen; rewrite -has_cat=>/hasP[it + it2].
by rewrite mem_cat=> infclc; exists it=> //; rewrite !mem_cat orbCA infclc orbT.
Qed.

End proof_environment.

Notation open_cell_side_limit_ok :=
  (@open_cell_side_limit_ok R).

Lemma step_sub_open_edges bottom top open closed open' closed' ev:
  cells_bottom_top bottom top open ->
  adjacent_cells open ->
  seq_valid open (point ev) ->
  out_left_event ev ->
  inside_box bottom top (point ev) ->
  step ev open closed = (open', closed') ->
  {subset [seq low i | i <- open'] ++ [seq high i | i <- open']
      <= [seq low i | i <- open] ++ [seq high i | i <- open] ++
         outgoing ev}.
Proof.
move=> cbtom adj sval oute inbox_e.
rewrite /step.
case oe : (open_cells_decomposition open (point ev)) => [[[[fc cc] lc] le] he].
have ocd := decomposition_preserve_cells oe.
have [c1 [c2 [c1in [c2in]]]] := l_h_in_open cbtom adj inbox_e.
rewrite oe => /= [[leeq heeq]] [] <- _.
rewrite -leeq -heeq; set nc := opening_cells _ _ _ _.
have memf (f : cell -> edge) mdc : [seq f i | i <- fc ++ mdc ++ lc] =i
        [seq f i | i <- fc ++ lc] ++ [seq f i | i <- mdc].
  move=> x; apply/mapP/idP.
    move=> [y + ->]; rewrite !mem_cat=>/orP[ | /orP[]] yin.
    - by apply/orP; left; apply/map_f; rewrite mem_cat yin.
    - by apply/orP; right; apply/map_f.
    by apply/orP; left; apply/map_f; rewrite mem_cat yin orbT.
  by rewrite mem_cat=>/orP[]/mapP[y + ->];[rewrite mem_cat=>/orP[] |];
    move=> yin; exists y; rewrite // !mem_cat ?yin ?orbT.
move=> i; rewrite mem_cat=> tmp.
rewrite ocd !mem_cat -[X in [|| X, _ | _]]orbb -{1}ocd. 
rewrite -[X in [|| _, X | _]]orbb -{2}ocd 2!memf.
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
case/orP: tmp; rewrite !memf !mem_cat; move=>/orP[->|]; rewrite ?orbT //.
  move/mapP=> [c cin ->].
  have:= opening_cells_subset vle vhe oute; rewrite -leeq -heeq.
  move=> /(_ _ cin); rewrite inE => /andP[] /orP[/eqP -> | +] _. 
    by rewrite map_f ?orbT //.
  by move=> ->; rewrite !orbT.
move/mapP=> [c cin ->].
have:= opening_cells_subset vle vhe oute; rewrite -leeq -heeq.
move=> /(_ _ cin). 
rewrite !inE => /andP[] _ /orP[/eqP -> | ->] . 
  by rewrite map_f ?orbT.
by rewrite ?orbT.
Qed.

Lemma inside_box_left_ptsP bottom top p :
  inside_box bottom top p -> left_limit (start_open_cell bottom top)  < p_x p.
Proof.
move=> /andP[] _ /andP[] valb valt.
move: valb valt=> /andP[] pgelb plerb /andP[] pgelt plert.
rewrite /start_open_cell/left_limit/leftmost_points; case: ifP=> cmpl.
  have /exists_point_valid [p1 p1P] : valid_edge bottom (left_pt top).
    rewrite /valid_edge (ltW cmpl) /=.
    by apply: ltW; apply: (lt_trans pgelt).
  rewrite p1P /=.
  by move: (intersection_on_edge p1P) => [] _ <-.
move/negbT: cmpl; rewrite -leNgt=>cmpl.
have /exists_point_valid [p1 p1P] : valid_edge top (left_pt bottom).
  rewrite /valid_edge cmpl /=.
  by apply/ltW; apply: (lt_trans pgelb).
by rewrite p1P /=.
Qed.

Lemma start_cover (bottom top : edge) (s : seq edge) closed open :
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, no_crossing R} ->
  all (inside_box bottom top) [seq left_pt x | x <- s] ->
  all (inside_box bottom top) [seq right_pt x | x <- s] ->
  start (edges_to_events s) bottom top = (closed, open) ->
  forall p, inside_box bottom top p ->
  has (inside_closed' p) closed || has (inside_open' p) open.
Proof.
move=> boxwf boxwf2 nocs leftin rightin; rewrite /start.
set evs := edges_to_events s.
have/perm_mem := edges_to_events_no_loss s.
  rewrite -/evs/events_to_edges/= => stoevs.
set op0 := [:: Bcell (leftmost_points bottom top) [::] bottom top].
set cl0 := (X in scan _ _ X).
have : sorted (@lexPt R) [seq point x | x <- evs].
  by apply: sorted_edges_to_events.
have : cells_bottom_top bottom top op0.
  by rewrite /op0/cells_bottom_top/cells_low_e_top/= !eqxx.
have : adjacent_cells op0 by [].
have : s_right_form op0 by rewrite /= boxwf.
have : close_alive_edges bottom top op0 evs.
  by rewrite /=/end_edge !inE !eqxx !orbT.
have : {in cell_edges op0 ++ flatten [seq outgoing i | i <- evs] &,
         no_crossing R}.
  rewrite /=; move: nocs; apply sub_in2.
  move=> x; rewrite !inE => /orP[ -> // | /orP[-> // | ]]; rewrite ?orbT //.
  by rewrite -stoevs => ->; rewrite ?orbT.
have : {in evs, forall ev, out_left_event ev}.
  by apply: out_left_edges_to_events.
have : close_edges_from_events bottom top evs.
  by apply: edges_to_events_wf.
have evsin0 : all (inside_box bottom top)
    [seq point ev | ev <- evs].
  apply/allP.
  have : {subset [seq right_pt g | g <- s] <= inside_box bottom top}.
    by apply/allP: rightin.
  have : {subset [seq left_pt g | g <- s] <= inside_box bottom top}.
    by apply/allP: leftin.
  by apply: edges_to_events_subset.
have btm_left0 : {in [seq point e | e <- evs], 
         forall e,  bottom_left_cells_lex op0 e}.
  move=> ev /[dup] /(allP evsin0) /andP[_ /andP[valb valt]] evin c.
  rewrite /op0 inE /lexPt /bottom_left_corner=> /eqP -> /=.
  by apply/orP; left; apply/inside_box_left_ptsP/(allP evsin0).
have sval0 :
  evs != nil -> seq_valid op0 (head dummy_pt [seq point ev | ev <- evs]).
  case evseq : evs => [// | ev evs'] _ /=; rewrite andbT.
  move: evsin0; rewrite evseq /= => /andP[] /andP[] _ /andP[] ebot etop _.
  have betW : forall a b c : R, a < b < c -> a <= b <= c.
    by move=> a b c /andP[] h1 h2; rewrite !ltW.
  by rewrite /valid_edge !betW.
have cov0 : forall p, all (lexePt p) [seq point ev | ev <- evs] ->
         cover_left_of bottom top p op0 cl0.
  move=> p limrp q inbox_q qp; apply/orP; left; apply/hasP.
  exists (Bcell (leftmost_points bottom top) nil bottom top).
    by rewrite /op0 inE eqxx.
  rewrite inside_open'E.
  apply/andP; split;[ | apply/andP; split].
  - by apply: underW; move: inbox_q=> /andP[] /andP[].
  - by move: inbox_q=> /andP[] /andP[].
  - rewrite /open_limit /=.
    case: (ltrP  (p_x (right_pt bottom)) (p_x (right_pt top))) => _.
    rewrite inside_box_left_ptsP //.
    by move: inbox_q => /andP[] _ /andP[] /andP[] _ /ltW ->.
  rewrite inside_box_left_ptsP //.
  by move: inbox_q => /andP[] _ /andP[] _ /andP[] _ /ltW ->.
have leftlim0 : {in op0, forall c p, inside_box bottom top p ->
         left_limit c = p_x p ->
         contains_point' p c -> has (inside_closed' p) cl0}.
  move=> c + p; rewrite inE -[Bcell _ _ _ _]/(start_open_cell bottom top).
  move=> /eqP -> {c}.
  move/inside_box_left_ptsP/[swap].
  by rewrite (leftmost_points_max boxwf2)=> ->; rewrite lt_irreflexive.
move: cov0 evsin0 sval0 btm_left0 leftlim0; move=> {stoevs}.
elim: evs op0 cl0 => [ | ev evs' Ih]
   op cl main evsin sval btm_left llim clev oute noc clae rfo adj cbtom sortev.
  rewrite /= => [][] <- <- p inbox_p.
  have lexpp : lexePt p p by rewrite lexePt_eqVlt eqxx.
  by rewrite orbC; apply: (main p isT p inbox_p lexpp).
rewrite /=.
case stepeq : (step ev op cl) => [op' cl'].
move=> scaneq.
have inbox_e : inside_box bottom top (point ev).
  by apply: (allP evsin); rewrite map_f // inE eqxx.
have := sval isT; rewrite /= => sval'.
have oute' : out_left_event ev by apply: oute; rewrite inE eqxx.
have btm_left' : bottom_left_cells_lex op (point ev).
  by apply: btm_left; rewrite inE eqxx.
have cov : cover_left_of bottom top (point ev) op cl.
  apply: main=> /=; rewrite lexePt_eqVlt eqxx /=.
  move: sortev; rewrite /sorted /=.
  rewrite  (path_sortedE (@lexPt_trans R)) // => /andP[+ _].
  by apply: sub_all; exact: lexPtW.
have cov' : forall p : pt,
    all (lexePt p) [seq point ev0 | ev0 <- evs'] ->
    cover_left_of bottom top p op' cl'.
  have := step_keeps_cover sortev cbtom adj inbox_e sval' oute' rfo clae clev
           noc btm_left' llim stepeq cov.
  move=> it p; apply: it.
have evle : forall ev', ev' \in evs' -> lexPt (point ev) (point ev').
  move=> ev' ev'in.
  move: sortev=> /=; rewrite (path_sortedE (@lexPt_trans R))=> /andP[]/allP.
  by move=> /(_ (point ev')) + _; apply; apply map_f.
have svalr : evs' != [::] ->
       seq_valid op' (head dummy_pt [seq point ev0 | ev0 <- evs']).
  case evs'eq : evs' => [// | a q] /= _.
  have inbox_a : inside_box bottom top (point a).
    by apply: (allP evsin); rewrite evs'eq !inE eqxx orbT.
  have eva : lexPt (point ev) (point a).
    by apply: evle; rewrite evs'eq inE eqxx.
  have limra : forall e', e' \in evs' -> lexePt (point a) (point e').
    rewrite evs'eq => e'; rewrite inE => /orP[/eqP -> | e'q ].
      by rewrite lexePt_eqVlt eqxx.
    move: sortev=> /=; rewrite evs'eq=> /path_sorted/=; rewrite path_sortedE.
      by move=>/andP[]/allP/(_ (point e') (map_f (@point _) e'q))/lexPtW.
    exact: lexPt_trans.
  have := step_keeps_valid inbox_a inbox_e eva oute' rfo cbtom adj sval' clae
            clev limra stepeq.
  by [].
have btm_leftr:
   {in [seq point e | e <- evs'], forall e, bottom_left_cells_lex op' e}.
  have btm_left2 :=
    step_keeps_left_pts_inf inbox_e oute' rfo sval' adj cbtom clae clev
           noc btm_left' stepeq.
  by move=> evp /mapP [ev' ev'in ->]; apply/btm_left2/evle.
have evsinr : all (inside_box bottom top) [seq point ev' | ev' <- evs'].
  by move: evsin; rewrite /= => /andP[].
have clevr : close_edges_from_events bottom top evs'.
  by move: clev; rewrite /= => /andP[].
have outer :{in evs', forall ev0 : event, out_left_event ev0}.
  by move: oute; apply: sub_in1=> x xin; rewrite inE xin orbT.
have nocr : {in cell_edges op' ++ flatten [seq outgoing i | i <- evs'] &,
     no_crossing R}.
  move: noc; apply: sub_in2=> x.
  rewrite mem_cat=> /orP[].
    move/(step_sub_open_edges cbtom adj sval' oute' inbox_e stepeq)=> it.
    by rewrite /= /cell_edges catA -(catA _ _ (outgoing ev)) mem_cat it.
  by move=> xinf; rewrite /= !mem_cat xinf !orbT.
have claer : close_alive_edges bottom top op' evs'.
  by have := step_keeps_closeness inbox_e oute' rfo cbtom adj sval' clev
      clae stepeq.
have rfor : s_right_form op'.
  have noc1: {in  cell_edges op ++ outgoing ev &, no_crossing R}.
    move: noc; apply sub_in2=> x.
    rewrite mem_cat=> /orP[it| xino].
      by rewrite /= /cell_edges catA 2!mem_cat it.
    by rewrite /= !mem_cat xino !orbT.
  by apply: (step_keeps_right_form cbtom adj inbox_e sval' noc1 _ _ stepeq).
have adjr : adjacent_cells op'.
  by have := step_keeps_adjacent inbox_e oute' sval' cbtom stepeq adj.
have cbtomr : cells_bottom_top bottom top op'.
  by apply: (step_keeps_bottom_top inbox_e sval' adj cbtom oute' stepeq).
have sortev' : sorted (@lexPt R) [seq point x | x <- evs'].
  by move: sortev; rewrite /= => /path_sorted.
have llim' : {in op', forall c p, inside_box bottom top p ->
                  left_limit c = p_x p -> 
                  contains_point' p c -> has (inside_closed' p) cl'}.
  by apply: (step_keeps_cover_left_border cbtom adj inbox_e sval' oute' rfo clae
       clev noc btm_left' stepeq llim).
by have := Ih _ _ cov' evsinr svalr btm_leftr llim' clevr outer nocr claer
  rfor adjr cbtomr sortev' scaneq.
Qed.

Lemma cell_edges_start bottom top :
  cell_edges [::(start_open_cell bottom top)] = [:: bottom; top].
Proof. by []. Qed.

Lemma start_disjoint bottom top s closed open evs :
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq left_pt x | x <- s] ->
  all (inside_box bottom top) [seq right_pt x | x <- s] ->
  all (inside_box bottom top) [seq point e | e <- evs] ->
  sorted (@lexPtEv _) evs ->
  {subset flatten [seq outgoing e | e <- evs] <= s} ->
  {in evs, forall ev, out_left_event ev} ->
  close_edges_from_events bottom top evs ->
  start evs bottom top = (closed, open) ->
  {in closed &, disjoint_closed_cells R} /\
  {in open & closed, disjoint_open_closed_cells R}.
Proof.
move=> boxwf startok nocs' leftin rightin evin lexev evsub out_evs cle.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
rewrite /start.
set op0 := [:: start_open_cell bottom top].
set cl0 := (X in scan _ _ X).
have op0sok : all open_cell_side_limit_ok op0.
  by rewrite /= startok.
have cbtom0 : cells_bottom_top bottom top op0.
  by rewrite /op0/cells_bottom_top/cells_low_e_top/= !eqxx.
have adj0: adjacent_cells op0 by [].
have rf0: s_right_form op0 by rewrite /= boxwf.
have claev0 : close_alive_edges bottom top op0 evs.
  by rewrite /=/end_edge !inE !eqxx !orbT.
have noc0 : {in cell_edges op0 ++ flatten [seq outgoing i | i <- evs] &,
         no_crossing R}.
  rewrite /=; move: nocs; apply sub_in2.
  move=> x; rewrite !inE => /orP[ -> // | /orP[-> // | ]]; rewrite ?orbT //.
  by move=> /evsub ->; rewrite !orbT.
have evsin0 : all (inside_box bottom top) [seq point ev | ev <- evs].
  exact: evin.
have sval0 :
  evs != nil -> seq_valid op0 (head dummy_pt [seq point ev | ev <- evs]).
  case evseq : evs => [// | ev evs'] _ /=; rewrite andbT.
  move: evsin0; rewrite evseq /= => /andP[] /andP[] _ /andP[] ebot etop _.
  have betW : forall a b c : R, a < b < c -> a <= b <= c.
    by move=> a b c /andP[] h1 h2; rewrite !ltW.
  by rewrite /valid_edge !betW.
have dis0 : {in cl0 &, disjoint_closed_cells R} /\
            {in op0 & cl0, disjoint_open_closed_cells R} by [].
have edges_sub : {subset all_edges op0 evs <= [:: bottom, top & s]}.
  move=> e.
  rewrite mem_cat !inE => /orP[] /=; last first.
    by move=> /evsub => ->; rewrite !orbT.
  by move=>  /orP[] /eqP ->; rewrite eqxx ?orbT.
have op_dis0 : {in op0 &, disjoint_open_cells R}.
  by move=> g1 g2; rewrite !inE => /eqP <-; left; apply/esym/eqP.
have esp0 : edge_side evs op0.
  rewrite /edge_side /edge_side_prop.
  case evseq : evs => [ // | ev evs' /=].
  have pin : inside_box bottom top (point ev).
    by apply: (allP evsin0); rewrite evseq /= inE eqxx.
  rewrite (inside_box_valid_bottom_top pin); last by rewrite !inE eqxx orbT.
  move: pin => /andP[] _ /andP[] _ /andP[] -> ->.
  by case: ifP => //; case: ifP.
have right_lims0 :
    {in evs & cl0, forall ev c, right_limit c  <= p_x (point ev)}.
  by [].
move: op0sok op_dis0 dis0 evsin0 sval0 edges_sub evin lexev
 evsub cle claev0 out_evs rf0 adj0 cbtom0 noc0 esp0 right_lims0.
elim: evs op0 cl0 => [ | ev evs' Ih] /=.
  rewrite /= => op cl opsok op_disj disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  move=> [] <- <-; exact: disj.
move=> op cl osok odis [cdis ocdis] /andP[] inbox_e inbox
  /(_ isT) sval edges_sub /andP[] evin evsin lexev sub_all clee clae
  out_evs rfo adj cbtom noc esp right_lims_evs.
case stepeq : (step ev op cl)=> [open' closed'].
have noc2: {in [seq low c | c <- op] ++ [seq high c | c <- op] ++ outgoing ev &,
        forall e1 e2, inter_at_ext e1 e2}.
  apply: (sub_in2 _ nocs') => g gin; apply: edges_sub; rewrite mem_cat.
  move: gin; rewrite catA mem_cat=> /orP[-> // | /=].
  by rewrite /events_to_edges /= [X in _ || X]mem_cat orbCA => ->.
have noc3: {in cell_edges op ++ outgoing ev &, no_crossing R}.
  by apply: (sub_in2 _ noc)=> c cin; rewrite catA mem_cat cin.
have out_e : out_left_event ev by apply: out_evs; rewrite inE eqxx.
have lexv' : all [eta lexPtEv ev] evs'.
  by apply: (order_path_min (@lexPtEv_trans _)).
have right_lims : {in cl, forall c, right_limit c <= p_x (point ev)}.
  by move=> c; apply: right_lims_evs; rewrite inE eqxx.
have allin : all (inside_box bottom top) [seq point e | e <- evs'].
  by apply/allP=> g gin; apply: (allP inbox g).
have hdin : evs' != [::] -> inside_box bottom top 
   (head dummy_pt [seq point e | e <- evs']).
  case evs'eq : evs' => [ // | ev1 evs'' /=] _.
  by apply: (allP evsin); rewrite evs'eq /= inE eqxx.
have sval1 : evs' != [::] ->
    seq_valid open' (head dummy_pt [seq point ev0 | ev0 <- evs']).
  move=> /[dup] evs'n0; case evs'eq : evs' => [ // | ev1 evs''] _.
  have := (step_keeps_valid (hdin evs'n0) _ _ _ _ _ _ _ clae _ _ stepeq).
  rewrite -evs'eq; apply => //.
  * rewrite evs'eq /=.
    have := allP (order_path_min (@lexPtEv_trans _) lexev).
    by move=> /(_ ev1); rewrite evs'eq inE eqxx => /(_ isT).
  * move=> e2; rewrite evs'eq inE=> /orP[/eqP -> | ].
    ** by rewrite lexePt_refl.
    move=> e2in; apply: lexPtW.
    move: lexev=> /path_sorted; rewrite evs'eq.
    by move=>/(order_path_min (@lexPtEv_trans _))/allP /(_ _ e2in).
have clae' : close_alive_edges bottom top open' evs'.
  exact: (step_keeps_closeness inbox_e out_e rfo cbtom adj sval _ _ stepeq).
apply: Ih => //.
- by apply: (step_keeps_open_cell_side_limit cbtom adj inbox_e sval
             out_e rfo noc3  stepeq osok).
- by apply: (step_keeps_disjoint_open cbtom adj inbox_e sval rfo noc2
        odis out_e osok esp clae lexv' stepeq).
- exact: (step_keeps_disjoint cbtom adj _ _ _ _ _ _ _ _ _ _ _ clae _ stepeq).
- move=> g; rewrite mem_cat=> /orP[]; last first.
    move=> gin; apply: edges_sub; rewrite mem_cat orbC /events_to_edges /=.
    by rewrite mem_cat gin !orbT.
  move/(step_keeps_subset cbtom adj sval out_e inbox_e stepeq)=> gin.
  apply: edges_sub; rewrite mem_cat /events_to_edges /= [X in _ || X]mem_cat.
  by rewrite orbA -mem_cat gin.
- exact: (path_sorted lexev).
- by move=> g gin; apply: sub_all; rewrite mem_cat gin orbT.
- by move: clee=> /andP[].
- by move=> e ein; apply: out_evs; rewrite inE ein orbT.
- exact: (step_keeps_right_form cbtom adj inbox_e sval _ _ _ stepeq).
- exact: (step_keeps_adjacent inbox_e out_e sval cbtom stepeq).
- exact: (step_keeps_bottom_top inbox_e sval adj cbtom out_e stepeq).
- move=> g1 g2; rewrite mem_cat=> g1in; rewrite mem_cat=> g2in; apply: noc;
  rewrite mem_cat [X in _ || X]mem_cat.
    move: g1in=> /orP[ | ->]; last by rewrite !orbT.
    move/(step_keeps_subset cbtom adj sval out_e inbox_e stepeq)=> gin.
    by rewrite orbA -mem_cat gin.
  move: g2in=> /orP[ | ->]; last by rewrite !orbT.
  move/(step_keeps_subset cbtom adj sval out_e inbox_e stepeq)=> gin.
  by rewrite orbA -mem_cat gin.
- apply:(step_keeps_edge_side stepeq _ out_e _ cbtom)=> //.
  * by rewrite /= evin.
have right_lims' := step_keeps_closed_to_the_left cbtom adj sval inbox_e rfo
         stepeq right_lims.
move=> ev1 c ev1in cin.
apply: (le_trans (right_lims' c cin)).
have : lexPtEv ev ev1 by exact: (allP lexv' _ ev1in).
by move=>/orP[ | /andP[] + _]; rewrite ?le_eqVlt=> ->; rewrite ?orbT.
Qed.

Lemma start_edge_covering bottom top s (evs : seq event) open closed :
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in [:: bottom, top & s] &, forall e1 e2, inter_at_ext e1 e2} ->
  {in [:: bottom, top & s] & [seq point e | e <- evs],
     forall g e, non_inner g e} ->
  all (inside_box bottom top) [seq point e | e <- evs] ->
  sorted (@lexPtEv _) evs ->
  {subset flatten [seq outgoing e | e <- evs] <= s} ->
  uniq (flatten [seq outgoing e | e <- evs]) ->
  {in evs, forall ev : event, out_left_event ev} ->
  close_edges_from_events bottom top evs ->
  start evs bottom top = (closed, open) ->
  {in evs, forall ev, forall g, g \in outgoing ev ->
     edge_covered g open closed}.
Proof.
move=> boxwf startok nocs' nonin evin lexev evsub uni out_evs cle.
rewrite /start.
set op0 := [:: start_open_cell bottom top].
set cl0 := (X in scan _ _ X).
have op0sok : all open_cell_side_limit_ok op0.
  by rewrite /= startok.
have cbtom0 : cells_bottom_top bottom top op0.
  by rewrite /op0/cells_bottom_top/cells_low_e_top/= !eqxx.
have adj0: adjacent_cells op0 by [].
have rf0: s_right_form op0 by rewrite /= boxwf.
have claev0 : close_alive_edges bottom top op0 evs.
  by rewrite /=/end_edge !inE !eqxx !orbT.
have evsin0 : all (inside_box bottom top) [seq point ev | ev <- evs].
  exact: evin.
have sval0 :
  evs != nil -> seq_valid op0 (head dummy_pt [seq point ev | ev <- evs]).
  case evseq : evs => [// | ev evs'] _ /=; rewrite andbT.
  move: evsin0; rewrite evseq /= => /andP[] /andP[] _ /andP[] ebot etop _.
  have betW : forall a b c : R, a < b < c -> a <= b <= c.
    by move=> a b c /andP[] h1 h2; rewrite !ltW.
  by rewrite /valid_edge !betW.
have op0sub : {subset cell_edges op0 <= [:: bottom, top & s]}.
  by rewrite cell_edges_start=> g; rewrite !inE orbA=> ->.
move=> scaneq.
suff main: forall g, 
        edge_covered g op0 cl0 \/ g \in flatten [seq outgoing e | e <- evs] ->
        edge_covered g open closed.
  move=> e ein g gin; apply: main; right.
  by apply/flattenP; exists (outgoing e);[apply/map_f | ].
have btm_left0 : {in [seq point e | e <- evs], 
         forall e,  bottom_left_cells_lex op0 e}.
  move=> ev /[dup] /(allP evsin0) /andP[_ /andP[valb valt]] evin' c.
  rewrite /op0 inE /lexPt /bottom_left_corner=> /eqP -> /=.
  by apply/orP; left; apply/inside_box_left_ptsP/(allP evsin0).
have inj0 : {in op0 &, injective (@high R)}.
  by move=> c1 c2; rewrite !inE => + => /eqP <- /eqP ->.
move: cbtom0 adj0 rf0 claev0 evsin0 sval0 op0sok evin lexev evsub out_evs
  uni cle nonin op0sub btm_left0 inj0 scaneq.
(*****)
elim: evs op0 cl0 => [ | e evs Ih] op cl cbtom adj rfo clae allin sval' allok
  evin lexev evsub out_evs uni clev nonin opsub btm_left inj.
  by move=> /= -[] <- <- g [// | //].
rewrite /=.
case stepeq : (step e op cl) => [op' cl'] scaneq.
have inbox_e : inside_box bottom top (point e).
  by apply: (allP allin); rewrite map_f // inE eqxx.
have {sval'}sval : seq_valid op (point e) by apply: sval'.
have oute : out_left_event e by apply: out_evs; rewrite inE eqxx.
have cbtom' : cells_bottom_top bottom top op'.
  exact: (step_keeps_bottom_top inbox_e sval adj cbtom oute stepeq).
have adj' : adjacent_cells op'.
  exact: (step_keeps_adjacent inbox_e oute sval cbtom stepeq adj).
have noc : {in cell_edges op ++ outgoing e &, no_crossing R}.
  apply: inter_at_ext_no_crossing.
  apply: (sub_in2 _ nocs').
  move=> g; rewrite mem_cat=> /orP[ | ino]; first exact: opsub.
  by rewrite !inE evsub ?orbT //= mem_cat ino.
have rfo' : s_right_form op'.
  exact: (step_keeps_right_form cbtom adj inbox_e sval noc oute rfo stepeq).
have clae' : close_alive_edges bottom top op' evs.
  by apply: (step_keeps_closeness inbox_e oute rfo _ adj sval clev clae stepeq).
have allin' : all (inside_box bottom top) [seq point ev | ev <- evs].
  by apply/allP=> p pin; apply: (allP allin p); rewrite inE pin orbT.
move: lexev; rewrite /= path_sortedE; last by apply: lexPtEv_trans.
move=> /andP[] /allP=> lexev lexev1.
have sval' :
 evs != [::] -> seq_valid op' (head dummy_pt [seq point ev | ev <- evs]).
  case evsq : evs => [// | ev1 evs'] _ /=.
  rewrite evsq in lexev lexev1.
  have ele1: lexPt (point e) (point ev1) by apply: lexev; rewrite inE eqxx.
  move: lexev1; rewrite /= path_sortedE; last by apply: lexPtEv_trans.
  move=> /andP[] lexev1 lexev1'.
  have lexev2 : {in evs, forall e, lexePt (point ev1) (point e)}.
    move=> e'; rewrite evsq inE=> /orP[/eqP -> |]; first by apply:lexePt_refl.
   by move=> e'in; apply/lexPtW; apply: (allP lexev1).
  have ev1in : inside_box bottom top (point ev1).
    by apply: (allP allin); rewrite evsq map_f // !inE eqxx ?orbT.
  by apply: (step_keeps_valid ev1in inbox_e ele1 oute _ _ _ _ _ clev
            lexev2 stepeq).
have opok' :all open_cell_side_limit_ok op'.
  by apply: (step_keeps_open_cell_side_limit cbtom _ _ _ _ _ noc stepeq allok).
have evin' : all (inside_box bottom top) [seq point e | e <- evs].
  by apply/allP=> x xin; apply: (allP evin); rewrite /= inE xin ?orbT.
have evsub' : {subset flatten [seq outgoing e | e <- evs] <= s}.
  by move=> g gin; apply: evsub; rewrite /= mem_cat gin orbT.
have out_evs' : {in evs, forall ev, out_left_event ev}.
  by move=> e' e'in; apply: out_evs; rewrite /= inE e'in orbT.
have uni' : uniq (flatten [seq outgoing e | e <- evs]).
  by move: uni; rewrite /= cat_uniq=> /andP[] _ /andP[] _.
have clev' : close_edges_from_events bottom top evs.
  by move: clev=> /= /andP[].
have nonin' : {in [:: bottom, top & s] & [seq point e | e <- evs],
        forall g p, non_inner g p}.
   by move=> g p gin pin; apply nonin; rewrite //= inE pin orbT.
have opsub': {subset cell_edges op' <= [:: bottom, top & s]}.
  move=> g /(step_keeps_subset cbtom adj sval oute inbox_e stepeq); rewrite mem_cat.
  move=> /orP[/opsub //| gout ].
  move: evsub=> /= /(_ g); rewrite mem_cat gout !inE=> -> //.
  by rewrite !orbT.  
have noc1 : {in all_edges op (e :: evs) &, no_crossing R}.
  apply: inter_at_ext_no_crossing.
  apply: (sub_in2 _ nocs').
  move=> g; rewrite mem_cat=> /orP[].
    by apply: opsub.
  by move/evsub; rewrite !inE => ->; rewrite ?orbT.
have btm_left_e : bottom_left_cells_lex op (point e).
  by apply: btm_left; rewrite map_f // inE eqxx.
have btm_left' : {in [seq point e | e <- evs], forall p, bottom_left_cells_lex op' p}.
  have btm_left2 :=
    step_keeps_left_pts_inf inbox_e oute rfo sval adj cbtom clae clev
           noc1 btm_left_e stepeq.
  by move=> p /mapP [ev' ev'in ->]; apply/btm_left2/lexev.
have ninnere : open_non_inner_event op e.
  rewrite /open_non_inner_event.
  move=> c cin; apply: nonin.
    by apply: opsub; rewrite mem_cat map_f ?orbT.
  by rewrite inE eqxx.
have inj' : {in op'&, injective (@high R)}.
  have unie : uniq (outgoing e).
    by move: uni; rewrite /= cat_uniq => /andP[].
  have hlex := bottom_left_lex_to_high cbtom adj rfo allok inbox_e btm_left_e.
  by apply : (step_keeps_injective_high cbtom _ _ _ _ _ unie hlex stepeq inj).
have {}Ih:= (Ih op' cl' cbtom' adj' rfo' clae' allin' sval' opok' evin' lexev1
         evsub' out_evs' uni' clev' nonin' opsub' btm_left' inj' scaneq ).
have step_edge_covering:=
   (step_keeps_edge_covering allok btm_left_e ninnere inj cbtom adj inbox_e
       sval rfo oute _ stepeq).
move=> g [gc | gev].
  by apply: Ih; left; apply: step_edge_covering; left.
move: gev; rewrite mem_cat=> /orP[gout | gev].
  by apply: Ih; left; apply: step_edge_covering; right.
by apply: Ih; right.
Qed.

End working_environment.
 
