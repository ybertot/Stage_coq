From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import math_comp_complements points_and_edges events cells.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section subset_tactic.

Lemma all_sub [T : eqType] [p : pred T] [s1 s2 : seq T] :
  {subset s1 <= s2} -> all p s2 -> all p s1.
Proof.  by move=> subs as2; apply/allP=> x xin; apply/(allP as2)/subs. Qed.

Lemma subset_consl [T : eqType] (x : T) (s s': seq T) :
  x \in s' -> {subset s <= s'} -> {subset (x :: s) <= s'}.
Proof.
by move=> xin ssub g; rewrite inE=> /orP[/eqP -> // | ]; apply: ssub.
Qed.

Lemma subset_catl [T : eqType] (s1 s2 s' : seq T) :
  {subset s1 <= s'} -> {subset s2 <= s'} -> {subset s1 ++ s2 <= s'}.
Proof.
move=> s1sub s2sub g; rewrite mem_cat=>/orP[];[apply: s1sub | apply s2sub].
Qed.

Lemma subset_catrl [T : eqType] [s s1 s2 : seq T] :
  {subset s <= s1} -> {subset s <= s1 ++ s2}.
Proof. by move=> ssub g gn; rewrite mem_cat ssub. Qed.

Lemma subset_catrr [T : eqType] [s s1 s2 : seq T] :
  {subset s <= s2} -> {subset s <= s1 ++ s2}.
Proof. by move=> ssub g gn; rewrite mem_cat ssub ?orbT. Qed.

Lemma subset_id [T : eqType] [s : seq T] : {subset s <= s}.
Proof. by move=> x. Qed.

Lemma subset_head [T : eqType] [s1 s2 : seq T] [x : T] :
  {subset (x :: s1) <= s2} -> head x s1 \in s2.
Proof. 
by move=> sub; apply: sub; case: s1=> [ | a ?] /=; rewrite !inE eqxx ?orbT.
Qed.

End subset_tactic.

Ltac subset_tac :=
  trivial; 
  match goal with
  | |- {subset ?x <= ?x} => apply: subset_id
  | |- {subset (_ :: _) <= _} => apply: subset_consl; subset_tac
  | |- {subset (_ ++ _) <= _} => apply: subset_catl; subset_tac
  | |- {subset _ <= _ ++ _} => 
     solve[(apply: subset_catrl; subset_tac)] || 
     (apply: subset_catrr; subset_tac)
  | |- {subset _ <= _} =>
    let g := fresh "g" in let gin := fresh "gin" in
    move=> g gin; rewrite !(mem_cat, inE, cat_rcons);
    rewrite ?eqxx ?gin ?orbT //; subset_tac
  | |- is_true (?x \in (?x :: _)) => rewrite inE eqxx; done
  | |- is_true (head _ (rcons _ _) \in _) => rewrite head_rcons; subset_tac
  | |- is_true (head _ _ \in _) => apply: subset_head; subset_tac
  | |- is_true (_ \in (_ :: _)) => rewrite inE; apply/orP; right; subset_tac
  | |- is_true (_ \in (_ ++ _)) => rewrite mem_cat; apply/orP;
    (solve [left; subset_tac] || (right; subset_tac))
  end.

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

Definition set_left_pts (c : cell) (l : seq pt) :=
  {| left_pts := l; right_pts := right_pts c; low := low c; high := high c |}.

Definition set_pts (c : cell) (l1 l2 : seq pt) :=
  {| left_pts := l1; right_pts := l2; low := low c; high := high c |}.

(* This function is to be called only when the event is in the middle
  of the last opening cell.  The point e needs to be added to the left
  points of one of the newly created open cells, but the one that receives
  the first segment of the last opening cells should keep its existing
  left points.*)
Definition update_open_cell (c : cell) (e : event) : seq cell * cell :=
  let ps := left_pts c in
  if outgoing e is nil then
    ([::], set_left_pts c [:: head dummy_pt ps, point e & behead ps])
  else
    match
    opening_cells_aux (point e) (sort (@edge_below _) (outgoing e))
        (low c) (high c) with
    | ([::], c') => (* this is an absurd case. *)
      ([::], c)
    | (c'::tlc', lc') =>
      (set_left_pts c' (point e :: behead ps) :: tlc', lc')
    end.

Definition update_open_cell_top (c : cell) (new_high : edge) (e : event) :=
  if outgoing e is nil then
    let newptseq :=
(* when function is called, (point e) should alread be in the left points. *)
      [:: Bpt (p_x (point e)) (pvert_y (point e) new_high) &
          left_pts c] in
      ([::], Bcell newptseq (right_pts c) (low c) new_high)
  else
    match opening_cells_aux (point e) (sort (@edge_below _) (outgoing e))
        (low c) new_high with
    | ([::], lc) => (* this is not supposed to happen *) ([::], lc)
    | (f :: q, lc) =>
      (set_left_pts f (point e :: behead (left_pts c)) :: q, lc)
    end.

Definition step (e : event) (st : scan_state) : scan_state :=
   let p := point e in
   let '(Bscan op1 lsto op2 cls cl lhigh lx) := st in
   if (p_x p != lx) then
     let '(first_cells, contact_cells, last_contact, last_cells, 
           lower_edge, higher_edge) :=
       open_cells_decomposition (op1 ++ lsto :: op2) p in
     let closed := closing_cells p contact_cells in
     let last_closed := close_cell p last_contact in
     let closed_cells := cls ++ cl :: closed in
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
     let closed_cells := cls++ cl :: closed in
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
       (* we know lsto was just open, so that its left limit is lx
         and its right limit is bounded by p_x (right_pt lhigh), which
         is necessarily p_x (point e). lsto is necessarily the
         first cell of contact_cells.  So the first element of
         contact_cells should not be closed. It can just be
         disregarded. *)
     let closed := closing_cells p (seq.behead contact_cells) in
     let last_closed := close_cell p last_contact in
     let (new_opens, new_lopen) := update_open_cell_top lsto higher_edge e in
     Bscan (op1 ++ fc' ++ new_opens) new_lopen last_cells
          (closed ++ cl :: cls) last_closed higher_edge lx.

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

Lemma decomposition_main_properties open_cells p fc cc lcc lc le he:
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
by have[] := decomposition_main_properties oe exc.
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
   decomposition_main_properties oe (exists_cell cbtom adj inbox_p).
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
   decomposition_main_properties oe (exists_cell cbtom adj inbox_p).
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
have [ocd [lcc_ctn [allct [allnct [flcnct [heq leq]]]]]]:=
   decomposition_main_properties oe (exists_cell cbtom adj inbox_p).
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
  decomposition_main_properties oe (exists_cell cbtom adj inbox_p).
exists (head lcc cc), lcc.
by do 2 (split; first by rewrite ocd; subset_tac).
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
  decomposition_main_properties oe (exists_cell cbtom adj inbox_p).
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
by have [_ [_ [/(_ c) + _]]] := decomposition_main_properties oe exi.
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
have [ocd [lcc_ctn [allctn _]]]:= decomposition_main_properties oe
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
   decomposition_main_properties oe exi.
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
have [ocd _] := decomposition_main_properties oe exi.
have vfc : {in [seq high i | i <- first_cells], forall g, valid_edge g p}.
  move=> g /mapP[c cin geq]; apply: (seq_valid_high sval).
  by rewrite geq map_f //; rewrite ocd; subset_tac.
move=> g /mapP[c cin geq].
have [fc1 [fc2 fceq]] := mem_seq_split cin.
have cin' : c \in open by rewrite ocd; subset_tac.
have := seq_edge_below' adj rfo; rewrite ocd fceq -[c :: _]/([:: c] ++ _).
set w := head _ _; rewrite -!catA (catA fc1) map_cat cat_path=> /andP[] _.
have tr : {in [seq high i | i <- first_cells] & &, transitive (@edge_below R)}.
  apply: (edge_below_trans _ vfc); first by left; exact side_cond.
  move: noc; apply: sub_in2; rewrite /cell_edges ocd !map_cat.
  by subset_tac.
rewrite cats1 map_rcons last_rcons map_cat cat_path=> /andP[] + _.
rewrite (path_sorted_inE tr); last first.
  apply/allP=> g' g'cnd; rewrite -[is_true _]/(is_true (g' \in (map _ _))) fceq.
  move: g'cnd; rewrite inE => /orP[/eqP -> | /mapP [g'c g'in ->]]; rewrite map_f // .
    by subset_tac.
  by subset_tac.
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
   decomposition_main_properties oe exi.
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
have [ocd [_ [_ [_ [_ [heq leq]]]]]] := decomposition_main_properties oe exi.
have [pal puh vl vp _]:=
  decomposition_connect_properties rfo sval adj cbtom inbox_e oe.
rewrite under_pvert_y; last first.
  apply: (seq_valid_high sval).
  by rewrite map_f //; rewrite ocd; subset_tac.
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
  by rewrite ocd fceq; subset_tac.
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
by rewrite (map_f (fun c => pvert_y p (high c))) //; subset_tac.
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
have [ocd _] := decomposition_main_properties oe exi.
rewrite strict_under_pvert_y; last first.
  by apply/(seq_valid_low sval)/map_f; rewrite ocd; subset_tac.
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
  by rewrite ocd lceq Pab; subset_tac.
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
by rewrite (map_f (fun c => pvert_y p (low c))); subset_tac.
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

Lemma sort_edge_below_sorted s :
  {in s &, @no_crossing _} ->
  sorted (@edge_below R) (sort (@edge_below R) s).
Proof.
move=> noc.
have /sort_sorted_in : {in s &, total (@edge_below _)}.
  by move=> x1 x2 x1in x2in; apply/orP/noc.
by apply; apply: allss.
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
  by apply: sort_edge_below_sorted.
have /sub_in1/= trsf : {subset sort (@edge_below R) s <= s}.
  by move=> x; rewrite mem_sort.
move/trsf:outs => {}outs.
have [lin hin] : (low_e \in [:: low_e, high_e & s]) /\
   (high_e \in [:: low_e, high_e & s]).
  by split; rewrite !inE eqxx ?orbT.
have slho : {subset (sort (@edge_below _) s) <=
               [:: low_e, high_e & s]}.
  by move=> x; rewrite mem_sort => xin; rewrite !inE xin ?orbT.
move=> x xin.
have srt : sorted (@edge_below R) (low_e :: sort (@edge_below R) s).
  case sq : (sort (@edge_below R) s) => [// | a tl].
    rewrite -[sorted _ _]/((low_e <| a) && sorted (@edge_below R) (a :: tl)).
    rewrite -sq sorted_e andbT alla //.
    by rewrite -(mem_sort (@edge_below _)) sq inE eqxx.
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
have [_ [_ [_ [_ [_ [heq [leq _]]]]]]]:= decomposition_main_properties oe exi.
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

Lemma opening_cells_aux_side_limit' e s le he s' c':
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

Lemma opening_cells_aux_side_limit e s le he s' c':
  valid_edge le e -> valid_edge he e ->
  e >>= le -> e <<< he ->
  {in s, forall g, left_pt g == e} ->
  opening_cells_aux e s le he = (s', c') ->
  all open_cell_side_limit_ok (rcons s' c').
Proof.
move=> + vh.
elim : s le s' c'=> [ | g s Ih] le s' c' /= vl above under lg.
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
    have euh : e <<= he by apply: underW.
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
- by apply: onAbove.
by move: lg; apply: sub_in1 => g' gin; rewrite inE gin orbT.
Qed.

Lemma opening_cells_side_limit e s le he :
  valid_edge le e -> valid_edge he e ->
  e >>= le -> e <<< he ->
  {in s, forall g, left_pt g == e} ->
  all open_cell_side_limit_ok (opening_cells e s le he).
Proof.
move=> vle vhe ea eu lefts.
have lefts' : {in sort (@edge_below _) s, forall g, left_pt g == e}.
  by move=> g; rewrite mem_sort; apply: lefts.
have := opening_cells_aux_side_limit vle vhe ea eu lefts'.
rewrite /opening_cells.
case oca_eq : (opening_cells_aux _ _ _ _) => [so co].
by apply.
Qed.

Lemma opening_cells_below_high p e c s le he:
  (e >>> le) && (e <<< he) ->
  valid_edge le e ->
  valid_edge he e ->
  valid_edge he p -> (forall g, g \in s -> left_pt g == e) ->
  {in le::he::s &, no_crossing R} ->
  c \in opening_cells e s le he -> strict_inside_open p c -> p <<< he.
Proof.
move=> ebounds vle vhe vp gleft noc oc /andP[]/andP[] plhc _ lims.
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
have cok := opening_cells_side_limit vle vhe labove under gleft.
move: cok =>/allP/(_ c oc) {}cok.
by apply: (valid_high_limits cok); move: lims=> /andP[] -> /ltW ->.
Qed.

Lemma opening_cells_above_low p e c s le he:
  (e >>> le) && (e <<< he) ->
  valid_edge le e ->
  valid_edge he e ->
  valid_edge le p -> (forall g, g \in s -> left_pt g == e) ->
  {in le:: he :: s &, no_crossing R} ->
  c \in opening_cells e s le he -> strict_inside_open p c -> p >>> le.
Proof.
move=> ebounds vle vhe vp gleft noc oc /andP[]/andP[] _ palc lims.
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
have cok := opening_cells_side_limit vle vhe labove under gleft.
move: cok => /allP/(_ c oc) {}cok.
by apply: (valid_low_limits cok); move: lims=> /andP[] -> /ltW ->.
Qed.

Lemma fan_edge_below_trans (s : seq edge) p :
  {in s, forall g, left_pt g == p} ->
  {in s & &, transitive (@edge_below R)}.
Proof.
move=> lcnd g1 g2 g3 g1in g2in g3in.
by apply: trans_edge_below_out (eqP (lcnd _ _))(eqP (lcnd _ _))(eqP (lcnd _ _)).
Qed.

(* TODO : move this lemma to cells *)
Lemma inside_open_cell_valid c p1 : 
  open_cell_side_limit_ok c ->
  inside_open_cell p1 c -> 
  valid_edge (low c) p1 && valid_edge (high c) p1.
Proof.
move=> /andP[] ne /andP[] sxl /andP[] _ /andP[] /andP[] _ onh /andP[] _ onl.
move=> /andP[] _; rewrite /left_limit /open_limit=> /andP[] ge lemin.
apply/andP; split.
  apply/andP; split.
    by apply: le_trans ge; move: onl=> /andP[].
  apply: (le_trans lemin).
  by rewrite le_minl lexx.
apply/andP; split.
 apply: le_trans ge; move: onh=> /andP[].
 rewrite (eqP (allP sxl (head dummy_pt (left_pts c))_)) //.
 by apply: head_in_not_nil.
by rewrite le_minr in lemin; move: lemin=>/andP[].
Qed.

Lemma opening_cells_aux_disjoint (oe : seq edge) p le he s' c' :
    p >>> le -> p <<< he -> valid_edge le p -> valid_edge he p ->
    {in oe, forall g : edge, left_pt g == p} ->
    path (@edge_below R) le oe ->
    opening_cells_aux p oe le he = (s', c') ->
    {in rcons s' c' &, disjoint_open_cells R}.
Proof.
move=> pl ph vl vh leftg soe.
have {}pl : p >>= le by apply/negP=> pule; case/negP: pl; apply: underW.
elim: oe s' c' leftg le pl vl soe=> [ | og oe Ih] s' c' leftg le pl vl soe /=.
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
have leftg' : {in oe, forall g, left_pt g == p}.
  by move=> x xin; rewrite leftg // inE xin orbT.
have paog : p >>= og.
  by rewrite -(eqP (leftg og _)) ?left_pt_above // inE eqxx.
have vog : valid_edge og p.
  by rewrite valid_edge_extremities // leftg ?inE ?eqxx.
have soe' : path (@edge_below _) og oe.
  by move: soe=> /=/andP[] _.
by apply: (Ih so co leftg' og paog vog soe' oca_eq).
move=> c cin; right=> q.
have oc0q : opening_cells_aux p (og :: oe) le he = (W :: so, co).
  by rewrite /= oca_eq pvertE.
have /allP cok :=
   opening_cells_aux_side_limit vl vh (* lowhigh *) pl ph (* noc' *) leftg oc0q.
have Wk : open_cell_side_limit_ok W by apply: cok; rewrite /= inE eqxx.
apply/negP=> /andP[] /andP[] /[dup] /(inside_open_cell_valid Wk) /andP[] _.
move=> vhWq /andP[] /andP[] _ bhw _ _.
have leftg' : {in oe, forall g, left_pt g == p}.
  by move=> g gin; apply leftg; rewrite inE gin orbT.
have vog : valid_edge og p.
  by apply: valid_edge_extremities; rewrite leftg // inE eqxx.
have Wbc : high W <| low c.
  have /andP[lcin _] := opening_cells_aux_subset vog vh leftg' oca_eq cin.
  have loc_trans : {in og :: oe & &, transitive (@edge_below _)}.
    by apply: (@fan_edge_below_trans _ p).
  move: (soe); rewrite /= (path_sorted_inE loc_trans); last by apply/allP=> x.
  move=> /andP[] _ /andP[] /allP allbelow _.
  move: lcin; rewrite inE=> /orP[/eqP -> | ]; first by apply: edge_below_refl.
  by apply: allbelow.
move=> /andP[] qin /andP[] qalc _.
have vlcq : valid_edge (low c) q.
  have ck : open_cell_side_limit_ok c by apply: cok=> /=; rewrite inE cin orbT.
  by have /andP[] := (inside_open_cell_valid ck qin).
by move: qalc; rewrite (order_edges_viz_point' vhWq vlcq Wbc bhw).
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
  by case: exi => c cin A; exists c=> //; subset_tac.
have := decomposition_main_properties oca_eq exi0 =>
  -[ocd [lcc_ctn [allct [allnct [flnct [heq [leq [lein hein]]]]]]]].
have := decomposition_main_properties ocal_eq exi =>
  -[ocd' [lcc_ctn' [allct' [allnct' [flnct' [heq' [leq' [lein' hein']]]]]]]].
have svalf : seq_valid f p.
  by apply/allP=> x xin; apply: (allP sval); subset_tac.
have rfof : s_right_form f.
  by apply/allP=> x xin; apply: (allP rfo); subset_tac.
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
  by apply/allP=> x xin; apply: (allP rfo); subset_tac.
have svalf : seq_valid f p.
  by apply/allP=> x xin; apply: (allP sval); subset_tac.
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

Lemma open_cells_decomposition_single f l c p :
  adjacent_cells (f ++ c :: l) ->
  s_right_form (f ++ c :: l) ->
  seq_valid (f ++ c :: l) p ->
  p >>> low c ->
  p <<< high c ->
  open_cells_decomposition (f ++ c :: l) p =
    (f, nil, c, l, low c, high c).
Proof.
move=> adj srf sv pal puh.
have exi : exists2 c', c' \in (c :: l) & contains_point' p c'.
  by exists c;[ rewrite inE eqxx // | rewrite /contains_point' pal underW].
have := open_cells_decomposition_cat adj srf sv exi pal.
case ocl : (open_cells_decomposition (c :: l) p) =>
        [[[[[fc cc] lcc] lc] le] he].
move: ocl; rewrite /open_cells_decomposition /=.
have -> : contains_point p c.
  by rewrite /contains_point underWC // underW.
case lq : l => [ | c1 l'] /=.
  by move=> [] <- <- <- <- <- <-; rewrite cats0.
suff -> : contains_point p c1 = false.
  by move=> [] <- <- <- <- <- <-; rewrite cats0.
move: adj=> /adjacent_catW[] _; rewrite lq /= => /andP[] /eqP lc1q  _.
by rewrite /contains_point -lc1q puh.
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

Let lstoin : lsto \in open.
Proof.  by rewrite /open; subset_tac. Qed.

Hypothesis inbox_all : all inside_box
                ([seq left_pt g | g <- cell_edges open] ++
                [seq right_pt g | g <- cell_edges open] ++
                [seq point x | x <- (e :: future_events)]).

Let inbox_e : inside_box (point e).
Proof.
apply: (allP inbox_all (point e)).
rewrite !mem_cat map_f ?orbT //; subset_tac.
Qed.

Let inbox_es : all inside_box [seq point x | x <- future_events].
Proof.
apply/allP=> x xin; apply: (allP inbox_all).
by rewrite /= !(mem_cat, inE) xin !orbT.
Qed.

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
Hypothesis pwo : pairwise (@edge_below _) (bottom :: [seq high c | c <- open]).
Hypothesis btom_left_corners :
  {in open, forall c, lexPt (bottom_left_corner c) (point e)}.  
Hypothesis open_side_limit : all open_cell_side_limit_ok open.
Hypothesis lex_left_limit :
  all (fun x => lexPt x (point e)) (behead (left_pts lsto)).
Hypothesis disjoint_open : {in open &, disjoint_open_cells R}.
Hypothesis disjoint_open_closed :
  {in open & rcons cls lstc, disjoint_open_closed_cells R}.
Hypothesis disjoint_closed : {in rcons cls lstc &, disjoint_closed_cells R}.
Hypothesis closed_right_limit :
 {in rcons cls lstc, forall c, right_limit c <= p_x (point e)}.
Hypothesis uniq_closed : uniq (rcons cls lstc).
Hypothesis non_empty_closed :
  {in rcons cls lstc, forall c, exists p, inside_closed' p c}.
Hypothesis non_empty_right : right_pts lstc != [::].
Hypothesis uniq_out : uniq (outgoing e).
Hypothesis high_inj : {in open &, injective (@high _)}.
Hypothesis btm_left : bottom_left_cells_lex open (point e).
Hypothesis uniq_open : uniq open.
Hypothesis closed_to_left :
  {in rcons cls lstc, forall c, right_limit c <= p_x (point e)}.
Hypothesis left_pt_open_lex :
  {in open & (e :: future_events), forall c e',
    lexPt (left_pt (high c)) (point e')}.

Lemma disoc_i i j s : (i < j < size s)%N ->
  adjacent_cells s ->
  pairwise (@edge_below _) [seq high c | c <- s] ->
  all open_cell_side_limit_ok s ->
  o_disjoint_e (nth dummy_cell s i) (nth dummy_cell s j).
Proof.
move=> + adjs pws open_side_limit_s.
move=> /andP[] iltj jlts.
have ilts : (i < size s)%N by apply: ltn_trans jlts.
set x := nth dummy_cell s i.
set y := nth dummy_cell s j.
have iin : x \in s by apply: mem_nth.
have jin : y \in s by apply: mem_nth.
have xok : open_cell_side_limit_ok x by apply: (allP open_side_limit_s).
have yok : open_cell_side_limit_ok y by apply: (allP open_side_limit_s).
right=> q; apply/negP=> /andP[].
move=> /andP[] /[dup] inx /(inside_open_cell_valid xok) /andP[] _ vhx _.
move=> /andP[] /[dup] iny /(inside_open_cell_valid yok) /andP[] vly _.
move=> /andP[] qay _.
move: inx=> /andP[] /andP[] _ quhx _.
case/negP:qay.
move: iltj; rewrite leq_eqVlt=> /orP[/eqP/esym jq | ].
  move: adjs.
  rewrite -(cat_take_drop j.+1 s)=> /adjacent_catW[] + _.
  rewrite (take_nth dummy_cell jlts) -/y jq (take_nth dummy_cell ilts) -/x.
  rewrite -2!cats1 -catA /= =>/adjacent_catW[] _ /=.
  by rewrite andbT=> /eqP <-.
move=> i1ltj.
set j' := j.-1.
have jj : j = j'.+1 by rewrite (ltn_predK i1ltj).
have j'lts : (j' < size s)%N.
  by apply: ltn_trans jlts; rewrite jj.
have iltj' : (i < j')%N by rewrite -ltnS -jj.
move: adjs.
rewrite -(cat_take_drop j.+1 s)=> /adjacent_catW[] + _.
rewrite (take_nth dummy_cell jlts) -/y jj (take_nth dummy_cell j'lts).
rewrite -2!cats1 -catA /= =>/adjacent_catW[] _ /= /andP[] /eqP lyq _.
apply: (order_edges_viz_point' vhx) => //.
rewrite -lyq.
move: pws => /(pairwiseP dummy_edge) /(_ i j') /=; rewrite size_map 2!inE.
move=> /(_ ilts j'lts iltj').
by rewrite -[dummy_edge]/(high dummy_cell) !(nth_map dummy_cell).
Qed.

Lemma disoc s:
  adjacent_cells s ->
  pairwise (@edge_below _) [seq high c | c <- s] ->
  all open_cell_side_limit_ok s ->
 {in s &, disjoint_open_cells R}.
Proof.
move=> adjs pws sok.
move=> x y xin yin.
set i := find (pred1 x) s.
set j := find (pred1 y) s.
case : (leqP i j) => [ | jlti]; last first.
  have ilts : (i < size s)%N by rewrite -has_find has_pred1.
  have jint : (j < i < size s)%N by rewrite jlti ilts.
  move: xin; rewrite -has_pred1=> /(nth_find dummy_cell) => /eqP <-.
  move: yin; rewrite -has_pred1=> /(nth_find dummy_cell) => /eqP <-.
  by apply/o_disjoint_eC/disoc_i.
rewrite leq_eqVlt=> /orP[/eqP ij | iltj].
  move: xin; rewrite -has_pred1=> /(nth_find dummy_cell) /= /eqP.
  rewrite -/i ij /j.
  move: yin; rewrite -has_pred1=> /(nth_find dummy_cell) /= /eqP -> ->.
  by left.
have jlto : (j < size s)%N by rewrite -has_find has_pred1.
have jint : (i < j < size s)%N by rewrite iltj jlto.
move: xin; rewrite -has_pred1=> /(nth_find dummy_cell) => /eqP <-.
move: yin; rewrite -has_pred1=> /(nth_find dummy_cell) => /eqP <-.
by apply/disoc_i.
Qed.

(* Thanks to the disoc lemma, we only need to prove that the high edges
  of all open cells satisfy the pairwise propserty for edge_below to
  obtain disjointness of cells. *)

Lemma opening_cells_aux_absurd_case le he (s : seq edge) :
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  s != [::] ->
  {in s, forall g, left_pt g == point e} ->
   (opening_cells_aux (point e) (sort (@edge_below _) s) le he).1 != [::].
Proof.
move=> vle vhe + outs; case sq : s => [ // | a s'] _.
case ssq : (sort (@edge_below _) s) => [ | b s2].
  by suff : a \in [::];[ | rewrite -ssq mem_sort sq inE eqxx].
rewrite -sq ssq /= pvertE //.
by case oca_eq : (opening_cells_aux _ _ _ _).
Qed.

Lemma inside_box_valid_bottom x : inside_box x -> valid_edge bottom x.
Proof.
move=> /andP[] _ /andP[] /andP[] /ltW + /ltW + _; rewrite /valid_edge.
by move=> -> ->.
Qed.

Lemma bottom_edge_below :
  {in cell_edges open, forall g, bottom <| g}.
Proof.
move=> g gin'.
have bin : bottom \in all_edges open (e :: future_events).
  suff ? : bottom \in [seq low c | c <- open].
    by rewrite /all_edges/cell_edges; subset_tac.
  have := cbtom=> /andP[]; case: (open) => //= c0 open' /eqP -> _.
  by subset_tac.
have gin : g \in all_edges open (e :: future_events).
  by rewrite /all_edges; subset_tac.
have /no_crossingE := noc gin bin.
have /[dup] /inside_box_valid_bottom -> : inside_box (left_pt g).
  by apply: (allP inbox_all); rewrite mem_cat map_f.
by move=> /andP[] /andP[] -> _ _ /(_ isT) [] _; apply.
Qed.

Let bet_e : between_edges bottom top (point e).
Proof. by apply inside_box_between. Qed.

Let subo : {subset outgoing e <= all_edges open (e :: future_events)}.
Proof. by rewrite /all_edges; subset_tac. Qed.

Let subo' : {subset sort (@edge_below _) (outgoing e)
                 <= all_edges open (e :: future_events)}.
Proof.
by move=> x; rewrite mem_sort=> xo; apply: subo.
Qed.

Let exi : exists2 c, c \in open & contains_point' (point e) c.
Proof. by apply: (exists_cell cbtom adj bet_e). Qed.

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
  apply/allP=> x; rewrite mem_rcons=> xin; apply: (allP sval).
  by move: x xin; rewrite /open; change {subset lsto::fop <= open}; subset_tac.
have vfop : {in rcons fop lsto, forall c, valid_edge (high c) (point e)}.
  move=> c cin.
  have cin' : high c \in [seq high i | i <- open].
    by apply: map_f; rewrite /open -cat_rcons; subset_tac.
  by apply: (seq_valid_high sval cin').
have rfop : s_right_form (rcons fop lsto).
  by apply: all_sub rfo; rewrite /open -cat_rcons; subset_tac.
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

Definition state_open_seq (s : scan_state) :=
  sc_open1 s ++ lst_open s :: sc_open2 s.

Definition state_closed_seq (s : scan_state) := 
  rcons (sc_closed s) (lst_closed s).

Definition inv1_seq (s : seq cell) :=
  close_alive_edges s future_events /\ seq_valid s p /\
  adjacent_cells s /\ cells_bottom_top s /\ s_right_form s.

Definition invariant1 (s : scan_state) :=
  inv1_seq (state_open_seq s).

Let val_between g (h : valid_edge g (point e)) := 
  valid_between_events elexp plexfut h inbox_p.

Lemma invariant1_default_case :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) :=
      opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
  inv1_seq ((fc ++ nos) ++ lno :: lc).
Proof.
case oe : (open_cells_decomposition open (point e)) =>
 [[[[[fc cc] lcc] lc] le] he].
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe ncont] :=
    decomposition_connect_properties rfo sval adj cbtom bet_e oe.
case oca_eq:(opening_cells_aux _ _ _ _) => [nos nlsto].
rewrite /invariant1 /state_open_seq /=.
have dec_not_end :=
    decomposition_not_end rfo sval adj cbtom bet_e oe.
have close_fc : close_alive_edges fc future_events.
  suff/head_not_end : close_alive_edges fc (e :: future_events).
    by apply=> c0 cin; apply: dec_not_end; rewrite cin.
  by apply/allP=> c0 cin; apply: (allP clae); rewrite ocd; subset_tac.
have close_lc : close_alive_edges lc future_events.
  suff/head_not_end : close_alive_edges lc (e :: future_events).
    by apply=> c0 cin; apply: dec_not_end; rewrite cin orbT.
  by apply/allP=> c0 cin; apply: (allP clae); rewrite ocd; subset_tac.
have endle : end_edge le future_events.
  suff  : end_edge le (e :: future_events).
    rewrite /end_edge; move=> /orP[-> // | ] /= /orP[ | ->]; last first.
      by rewrite orbT.
    by move: pal=> /[swap] /eqP <-; rewrite right_pt_below.
  have := (proj1 (andP (allP clae (head lcc cc) _))); rewrite leq; apply.
  by rewrite ocd; subset_tac.
have endhe : end_edge he future_events.
  suff  : end_edge he (e :: future_events).
    rewrite /end_edge; move=> /orP[-> // | ] /= /orP[ | ->]; last first.
      by rewrite orbT.
    move: puh=> /[swap] /eqP <-; rewrite strict_nonAunder; last first.
      by apply: valid_edge_right.
    by rewrite right_on_edge.
  have := (proj2 (andP (allP clae lcc _))); rewrite ?heq; apply.
  by rewrite ocd; subset_tac.
move: cle => /= /andP[] cloe _.
have clan := opening_cells_close vle vhe oute endle endhe cloe.
have main := (insert_opening_closeness close_fc clan close_lc).
split.
  by move: main; rewrite /opening_cells oca_eq -cats1 -!catA.
have subfc : {subset fc <= open} by rewrite ocd; subset_tac.
have sublc : {subset lc <= open} by rewrite ocd; subset_tac.
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
have lein' : le \in all_edges open (e :: future_events).
  by rewrite /all_edges; subset_tac.
have hein' : he \in all_edges open (e :: future_events).
  by rewrite /all_edges; subset_tac.
have lebhe : le <| he.
  by apply: (edge_below_from_point_above (noc _ _) vle vhe (underWC _)).
have noc2 : {in [:: le, he & outgoing e] &, no_crossing R}.
  by apply: (sub_in2 _ noc); rewrite /all_edges; subset_tac.
have subso : {subset sort (@edge_below _) (outgoing e)
                <= all_edges open (e :: future_events)}.
  by move=> x; rewrite mem_sort; apply: subo.
apply/allP=> x; rewrite 2!mem_cat orbCA => /orP[xin | xold]; last first.
  by apply: (allP rfo); rewrite ocd; move: xold => /orP[] ?; subset_tac.
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
case oca_eq : (opening_cells_aux _ _ _ _) => [[ // | fno nos] lno] [] <- <-.
  have onn : outgoing e != [::] by rewrite o_eq.
  by have := opening_cells_aux_absurd_case vlo vho onn oute; rewrite oca_eq.
rewrite /= last_rcons.
have [/= A ->] := adjacent_opening_aux' vlo vho oute' oca_eq.
split;[ | split]=> //=.
  have := opening_cells_aux_high_last vlo vho oute'.
  by rewrite oca_eq /=.
by move: A; case : (nos).
Qed.

Let loin : low lsto \in all_edges open (e :: future_events).
Proof. by rewrite 2!mem_cat map_f. Qed.

Let hoin : high lsto \in all_edges open (e :: future_events).
Proof. by rewrite 2!mem_cat map_f // orbT. Qed.

Lemma low_all_edges c evs: c \in open -> low c \in all_edges open evs.
Proof. by move=> cin; rewrite !mem_cat map_f ?orbT. Qed.

Lemma high_all_edges c evs: c \in open -> high c \in all_edges open evs.
Proof. by move=> cin; rewrite !mem_cat map_f ?orbT. Qed.

Let open_edge_valid x :
   x \in cell_edges open -> valid_edge x (point e).
Proof.
by rewrite /cell_edges mem_cat => /orP[] /mapP [c /(allP sval) /andP[]+ + ->].
Qed.

Lemma update_open_cell_right_form  new_op new_lsto:
  update_open_cell lsto e = (new_op, new_lsto) ->
  point e <<< high lsto ->
  point e >>> low lsto ->
  s_right_form (rcons new_op new_lsto).
Proof.
move=> + puho palo.
have noco : below_alt (low lsto) (high lsto).
  apply: noc; first by apply: low_all_edges; rewrite /open; subset_tac.
  by apply: high_all_edges; rewrite /open; subset_tac.
have rflsto : low lsto <| high lsto.
  by apply: (edge_below_from_point_above noco vlo vho (underWC _)).
rewrite /update_open_cell.
have srt : path (@edge_below _) (low lsto) (sort (@edge_below _) (outgoing e)).
  apply: (sorted_outgoing vlo vho palo puho oute).
  apply: sub_in2 noc=> x; rewrite 2!inE => /orP[/eqP ->  | /orP[/eqP -> | ]] //.
  by apply: subo.
case ogeq : (outgoing e) => [ | g os].
  move=> [] <- <- /=; rewrite andbT.
  by apply: (edge_below_from_point_above noco vlo vho (underWC _)).
case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
  move=> [] <- <- /=; rewrite andbT.
  rewrite -ogeq /= in oca_eq.
  have /= := opening_cells_aux_right_form (underWC palo)
  puho vlo vho loin hoin rflsto oute' noc subo' srt oca_eq.
  by rewrite andbT.
move=> [] <- <- /=.
rewrite -ogeq /= in oca_eq.
by have /= := opening_cells_aux_right_form (underWC palo)
puho vlo vho loin hoin rflsto oute' noc subo' srt oca_eq.
Qed.

Lemma last_step_situation fc' cc lcc lc le he:
  open_cells_decomposition (lsto :: lop) (point e) =
    (fc', cc, lcc, lc, le, he) ->
  p_x (point e) = lstx ->
  ~~ (point e <<< lsthe) ->
  point e <<= lsthe ->
  fc' = [::] /\ le = low lsto.
Proof.
move=> oe pxhere eabove ebelow.
have lsto_ctn : contains_point'(point e) lsto.
  by rewrite /contains_point' -lstheq ebelow abovelstle.
have exi2 : exists2 c, c \in (lsto :: lop) & contains_point' (point e) c.
  by exists lsto; rewrite // inE eqxx.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]]
  := decomposition_main_properties oe exi2.
have fc'0 : fc' = [::].
  case fc'q : fc' => [// | fc'i fc2].
  move: ocd; rewrite fc'q /= => - [] lstoisfc'i _.
  move: (all_nct lsto).
  by rewrite (contains_point'W lsto_ctn) fc'q lstoisfc'i inE eqxx =>/(_ isT).
have [ fopq | [fop' [lfop fopq]]] :
  fop = nil \/ exists fop' lfop, fop = rcons fop' lfop.
    elim/last_ind: (fop) => [| fop' lfop]; first by left.
    by right; exists fop', lfop.
  move: ocd; rewrite -cat_rcons fc'0 /= => lstohead.
  suff : lsto = head lcc cc by move=> ->.
  by rewrite -[LHS]/(head lsto (lsto :: lop)) lstohead; case: (cc).
move: adj; rewrite /open ocd fopq fc'0 cat_rcons /=.
move=> /adjacent_catW[] _ it.
move: (ocd); rewrite fc'0 /=; move: it=> /[swap] <- /andP[] /eqP <- _.
split;[done | apply/esym; rewrite leq].
move: adj; rewrite /open ocd fc'0 /= fopq cat_rcons=>/adjacent_catW[] _.
by case: (cc) => [ | cc0 cc'] /andP[] /eqP ->.
Qed.

Lemma update_open_cell_end_edge new_op new_lsto :
  end_edge (low lsto) future_events ->
  end_edge (high lsto) future_events ->
  valid_edge (low lsto) (point e) ->
  valid_edge (high lsto) (point e) ->
  update_open_cell lsto e = (new_op, new_lsto) ->
  {in rcons new_op new_lsto, forall x,
    end_edge (low x) future_events && end_edge (high x) future_events}.
Proof.
move=> endl endh vl vh.
rewrite /update_open_cell.
case ogeq : (outgoing e) => [ | fog ogs].
  move=> [] <- <- /= x; rewrite inE=> /eqP -> /=.
  by rewrite endl endh.
move: cle; rewrite /= => /andP[] cloe _.
have cllsto := opening_cells_close vl vh oute endl endh cloe => {cloe}.
case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
  have onn : outgoing e != [::] by rewrite ogeq.
  have := opening_cells_aux_absurd_case vlo vho onn oute.
  by rewrite ogeq oca_eq.
move=> -[] <- <- /= x; rewrite inE=> /orP[/eqP -> | xin].
  by rewrite /=; apply: (allP cllsto); rewrite /opening_cells ogeq oca_eq /=;
   subset_tac.
by apply: (allP cllsto); rewrite /opening_cells ogeq oca_eq /= inE xin orbT.
Qed.
  
Lemma update_open_cell_end_edge' c nos lno :
  valid_edge (low c) (point e) ->
  valid_edge (high c) (point e) ->
  update_open_cell c e = (nos, lno) ->
  close_alive_edges (rcons nos lno) future_events =
  close_alive_edges (opening_cells (point e) (outgoing e)
      (low c) (high c)) future_events.
Proof.
move=> vlc vhc; rewrite /update_open_cell.
case ogeq : (outgoing e) => [ | fog ogs].
  move=> -[] <- <- /=.
  by rewrite /opening_cells /= pvertE // pvertE.
rewrite /opening_cells /=.
have onn : outgoing e != [::] by rewrite ogeq.
have := opening_cells_aux_absurd_case vlc vhc onn oute; rewrite ogeq.
by case oca_eq : (opening_cells_aux _ _ _ _) => [[ | ? ?] ?] + [] <- <- /=.
Qed.

Lemma update_open_cell_valid c nos lno :
  valid_edge (low c) (point e) ->
  valid_edge (high c) (point e) ->
  update_open_cell c e = (nos, lno) ->
  seq_valid (rcons nos lno) p = 
  seq_valid (opening_cells (point e) (outgoing e) (low c) (high c)) p.
Proof.
move=> vlc vhc; rewrite /update_open_cell.
case ogeq : (outgoing e) => [ | fog ogs].
  move=> -[] <- <- /=.
  by rewrite /opening_cells /= pvertE // pvertE.
rewrite /opening_cells /=.
have onn : outgoing e != [::] by rewrite ogeq.
have := opening_cells_aux_absurd_case vlc vhc onn oute; rewrite ogeq.
by case oca_eq : (opening_cells_aux _ _ _ _) => [[ | ? ?] ?] + [] <- <- /=.
Qed.

Lemma inv1_seq_set_pts s1 s2 c1 lpts1 lpts2 :
  inv1_seq (s1 ++ set_pts c1 lpts1 lpts2 :: s2) <->
  inv1_seq (s1 ++ c1 :: s2).
Proof.
rewrite /inv1_seq.
have -> : close_alive_edges (s1 ++ set_pts c1 lpts1 lpts2 :: s2)
 future_events =
  close_alive_edges (s1 ++ c1 :: s2) future_events.
  by rewrite /close_alive_edges !all_cat /=.
have -> : seq_valid (s1 ++ set_pts c1 lpts1 lpts2 :: s2) p =
  seq_valid (s1 ++ c1 :: s2) p.
  by rewrite /seq_valid !all_cat /=.
have -> : adjacent_cells (s1 ++ set_pts c1 lpts1 lpts2 :: s2) =
  adjacent_cells (s1 ++ c1 :: s2).
  elim/last_ind : s1 => [ | [ | c0 s1] c0' _]; case: s2 => [ | c2 s2] //=;
  by rewrite /adjacent_cells ?cat_rcons ?cat_path //.
have -> : cells_bottom_top (s1 ++ set_pts c1 lpts1 lpts2 :: s2) =
  cells_bottom_top (s1 ++ c1 :: s2).
  rewrite /cells_bottom_top /cells_low_e_top.
  by case: s1 => [ | c0 s1]; elim/last_ind: s2 => [ | s2 c2 _];
   rewrite /= -?cat_rcons ?(last_rcons, cats0, last_cat).
have -> : s_right_form (s1 ++ set_pts c1 lpts1 lpts2 :: s2) =
  s_right_form (s1 ++ c1 :: s2).
  by rewrite /s_right_form !all_cat /=.
by [].
Qed.

Lemma inv1_seq_set_left_pts s1 s2 c1 lpts :
  inv1_seq (s1 ++ set_left_pts c1 lpts :: s2) <->
  inv1_seq (s1 ++ c1 :: s2).
Proof. exact (inv1_seq_set_pts s1 s2 c1 lpts (right_pts c1)). Qed.

Lemma step_keeps_invariant1 :
  invariant1 (step e (Bscan fop lsto lop cls lstc lsthe lstx)).
Proof.
case step_eq : (step _ _) => [fop' lsto' lop' cls' lstc' lsthe' lstx']. 
rewrite /state_open_seq /=; move: step_eq.
rewrite /step -/open.
have val_bet := valid_between_events elexp plexfut _ inbox_p.
case: ifP=> [pxaway | /negbFE/eqP/[dup] pxhere /abovelstle palstol].
  move: invariant1_default_case.
  case oe: (open_cells_decomposition _ _) => [[[[[fc cc ] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno] def_case.
  rewrite /inv1_seq /= in def_case.  
  move=> [] <- <- <- _ _ _ _.
  by apply: def_case.
have infop : {subset fop <= open} by rewrite /open; subset_tac.
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
have inlop : {subset lop <= open} by rewrite /open; subset_tac.
have lopclae : close_alive_edges lop (e :: future_events).
  by apply/allP=> x xin; apply: (allP clae x); apply inlop.
have fop_note x : x \in fop ->
  ~ event_close_edge (low x) e /\ ~ event_close_edge (high x) e.
  move=> xin; apply: contrapositive_close_imp_cont.
  - by apply: (allP rfo); rewrite /open; subset_tac.
  - by apply/andP; apply: (allP sval); rewrite /open; subset_tac.
  by apply: allnct1.
have fopclae : close_alive_edges fop (e :: future_events).
  by apply/allP=> x xin; apply: (allP clae); rewrite /open; subset_tac.
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
  have := invariant1_default_case.
  by rewrite oe' oca_eq  /= cat_rcons.
have /andP [vllsto vhlsto] : valid_edge (low lsto) (point e) &&
                       valid_edge (high lsto) (point e).
  by move: sval=> /allP/(_ lsto); rewrite /open; apply; subset_tac.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  case uoceq : (update_open_cell lsto e) => [ nos lno] <-.
  rewrite /invariant1 /= /state_open_seq /= -catA -cat_rcons.
  move: uoceq; rewrite /update_open_cell.
  case ogq : (outgoing e) => [ | fog ogs] /=.
    move=> -[] <- <- /=; rewrite inv1_seq_set_left_pts.
    have := invariant1_default_case.
    rewrite open_cells_decomposition_single=> //; last by rewrite -lstheq.
    rewrite ogq /= pvertE // pvertE //=; rewrite cats0.
    have /negbTE -> :
         {| p_x := p_x (point e); p_y := pvert_y (point e) (high lsto)|}
           != point e.
      rewrite pt_eqE /= eqxx /=.
      move: ebelow_st; rewrite strict_under_pvert_y lstheq // lt_neqAle eq_sym.
      by move=> /andP[].
    have /negbTE -> :
     point e != {|p_x := p_x (point e); p_y := pvert_y (point e) (low lsto) |}.
      rewrite pt_eqE /= eqxx /=.
      by move: palstol; rewrite under_pvert_y // le_eqVlt negb_or=> /andP[].
    set w := [:: _ ; _; _].
    by rewrite (inv1_seq_set_pts fop lop lsto w nil).
  have := invariant1_default_case.
  rewrite open_cells_decomposition_single=> //; last by rewrite -lstheq.
  rewrite ogq; case oca_eq: (opening_cells_aux _ _ _ _) => [[ | no0 nos'] lno'].
    have ognn : (outgoing e) != [::] by rewrite ogq.
    have := opening_cells_aux_absurd_case vlo vho ognn oute.
    by rewrite ogq oca_eq.
  by move => + [] <- <- /=; rewrite inv1_seq_set_left_pts cat_rcons -!catA /=.
have lsto_ctn : contains_point'(point e) lsto.
  by rewrite /contains_point' -lstheq (negbFE ebelow) abovelstle.
have exi2 : exists2 c, c \in (lsto :: lop) & contains_point' (point e) c.
  by exists lsto; rewrite // inE eqxx.
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
  rewrite oe => oe'.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
  decomposition_main_properties oe' exi.
have [ocd' _] := decomposition_main_properties oe exi2.
have [fc'0  lelsto] : fc' = [::] /\ le = low lsto.
  by have := last_step_situation oe pxhere (negbT eonlsthe) (negbFE ebelow).
rewrite /update_open_cell_top.
case o_eq : (outgoing e) => [ | g l]; rewrite -?o_eq; last first.
  have := invariant1_default_case; rewrite oe'.
  rewrite -lelsto.
  case: (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
    move=> + <-; rewrite /invariant1 /state_open_seq /=.
    by rewrite !cats0 -!catA.
  move=> + <-; rewrite /invariant1 /state_open_seq /=.
  rewrite -!catA /= => it.
  by rewrite (catA fop) inv1_seq_set_left_pts -catA.
move=> [] <- <- <- _ _ _ _ /=.
have subf : {subset (fop ++ fc') <= open} by rewrite /open ocd; subset_tac.
have adjf : adjacent_cells (fop ++ fc').
  by move: adj; rewrite /open ocd=> /adjacent_catW[].
have claef : close_alive_edges (fop ++ fc') (e :: future_events).
  by apply/allP=> x xin; apply: (allP clae); apply: subf.
have rfof : s_right_form (fop ++ fc').
  by apply/allP=> x xin; apply: (allP rfo); apply: subf.
have svalf : seq_valid (fop ++ fc') (point e).
  by apply/allP=> x xin; apply: (allP sval); apply: subf.
have subl : {subset (lsto :: lop) <= open}.
  by rewrite /open; subset_tac.
have adjl : adjacent_cells (lsto :: lop).
  by move: adj=> /adjacent_catW[].
have rfol : s_right_form (lsto :: lop).
  by apply/allP=> x xin; apply: (allP rfo); apply: subl.
have svall : seq_valid (lsto :: lop) (point e).
  by apply/allP=> x xin; apply: (allP sval); apply: subl.
have cbtom' : cells.cells_bottom_top (low lsto) top (lsto :: lop).
  move: cbtom; rewrite /open /cells.cells_bottom_top /cells_low_e_top eqxx //=.
  by move=> /andP[] _; rewrite last_cat /=.
have [pal puh vl vh not_ct] :=
  decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
have claef' : close_alive_edges (fop ++ fc') future_events.
  elim/last_ind: {-1}(fop ++ fc') (erefl (fop ++ fc')) => [// | fc2 c2 _] f_eq.
  have hc2q : high c2 = low (head lcc cc).
    move: adj; rewrite /open ocd catA f_eq -cats1 -!catA=> /adjacent_catW[] _.
    by rewrite /=; case: (cc) => [ | ? ?] /andP[] /eqP.
  have palst : point e >>> high (last dummy_cell (fop ++ fc')).
    by rewrite f_eq last_rcons hc2q -leq.
  have [above_l above_h] := above_all_cells svalf adjf rfof palst.
  have {}allabove_l : {in fop ++ fc', forall c, point e >>> low c}.
    move=> c /mem_seq_split [s1 [s2 s_q]].
      elim/last_ind : {-1} (s1) (erefl s1) => [ | s1' c1 _] s1q.
        by move: above_l; rewrite s_q s1q /=.
      have : point e >>> high c1.
        by rewrite above_h // s_q s1q cat_rcons; subset_tac.
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
  by apply/allP=> x xin; apply: (allP clae); rewrite /open ocd; subset_tac.
have clael' : close_alive_edges lc future_events.
  case lc_eq : (lc) => [ // | c2 lc2]; rewrite -lc_eq.
  have [puhlcc adj2] : point e <<< low (head dummy_cell lc) /\
                        adjacent_cells lc.
    move: adj; rewrite /open ocd lc_eq.
    move=> /adjacent_catW[] _ /adjacent_catW[] _ /=.
    by move=> /andP[] /eqP <- ->; rewrite -heq.
  have sub2 : {subset lc <= open} by rewrite /open ocd; subset_tac.
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
    move=> /andP[]/eqP <- _; apply: below_h.
    rewrite s_q s1_q cat_rcons; subset_tac.
  have l_not_end : forall c, c \in lc ->
  ~ event_close_edge (low c) e /\ ~ event_close_edge (high c) e.
    move=> c cin; apply: contrapositive_close_imp_cont.
    - by apply: (allP rfo2).
    - by apply/andP; apply: (allP sval2).
    by apply/negP; rewrite /contains_point negb_and negbK (below_l _ cin).
  apply/allP=> x xin.
  by apply: (allP (head_not_end clael l_not_end)).
rewrite cats0 /invariant1 /state_open_seq /=; set open' := (X in inv1_seq X).
have clae_part : close_alive_edges open' future_events.
  rewrite /close_alive_edges all_cat [all _ (fop ++ fc')]claef' /=.
  rewrite [all _ lc]clael' andbT.
  have le_end : end_edge le future_events.
    elim/last_ind : {-1} (fop ++ fc') (erefl (fop ++ fc')) => [ | fs c1 _] f_eq.
      move: f_eq; case fop_eq: (fop) => [ | //].
      move: cbtom; rewrite /open fop_eq /= => /andP[] /andP[] _ /= /eqP + _.
      by rewrite /end_edge lelsto !inE => -> _; rewrite eqxx.
    have <- : high c1 = le.
      rewrite fc'0 cats0 in f_eq.
      move: adj; rewrite /open f_eq -cats1 -catA=>/adjacent_catW[] _ /=.
      by rewrite lelsto; move=> /andP[] /eqP.
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
  by rewrite -lelsto le_end he_end.
split=> //.
rewrite /seq_valid all_cat /= all_cat andbCA.
have vhe : valid_edge he (point e).
 by have []:= decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
split.
  apply/andP; split; last first.
    rewrite -!all_cat fc'0 cats0; apply/allP=> x xin.
    have /andP[vlx vhx] :
    valid_edge (low x) (point e) && valid_edge (high x) (point e).
      apply: (allP sval); rewrite /open ocd.
      by move: xin; rewrite mem_cat=> /orP[] ?; subset_tac.
    have /andP[eelx eehx] :
     end_edge (low x) future_events && end_edge (high x) future_events.
      apply: (allP clae_part). 
      by rewrite /open'; move: xin; rewrite mem_cat=>/orP[] ?; subset_tac.
    by rewrite !val_between.
  have eelo : end_edge (low lsto) future_events.
    have : end_edge (low lsto) (e :: future_events).
      by apply: (proj1 (andP (allP clae lsto _))).
    rewrite /end_edge /= => /orP[-> // | /orP[abs | ->]]; last by rewrite !orbT.
    by move: palstol; rewrite -(eqP abs) right_pt_below.
  have eehe : end_edge he future_events.
    have : end_edge (high lcc) (e :: future_events).
      apply: (proj2 (andP (allP clae lcc _))).
      by rewrite /open ocd; subset_tac.
    rewrite /end_edge heq /= => /orP[-> // | /orP[abs | ->]]; last first.
      by rewrite orbT.
    by move: puh; rewrite heq -(eqP abs) -[_ <<< _]negbK right_pt_above.
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
  move: adj; rewrite /open ocd=> /adjacent_catW[] _ /adjacent_catW[] _ /=.
  by case: (lc) => [// | c2 l'] /=; rewrite heq.
have on0 : rcons cc lcc != nil by apply/eqP/rcons_neq0.
rewrite /open'.
set nc := Bcell _ _ _ _.
have nn0 : [:: nc] != nil by [].
split.
  rewrite -(replacing_seq_cells_bottom_top _ _ _ _ on0 nn0).
  - by rewrite cat_rcons -ocd.
  - rewrite /nc /= head_rcons.
    by rewrite -leq.
  by rewrite /nc/= last_rcons.
rewrite /s_right_form all_cat /=; apply/andP; split.
  by apply/allP=> x xin; apply: (allP rfo); rewrite /open ocd; subset_tac.
apply/andP; split; last first.
  by apply/allP=> x xin; apply: (allP rfo); rewrite /open ocd; subset_tac.
have noclstohe : below_alt he (low lsto).
  by apply: noc; rewrite /all_edges; subset_tac.
have := edge_below_from_point_under noclstohe vhe vlo (underW puh) palstol.
by [].
Qed.

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
  decomposition_main_properties oe exi.
have [pal puh vle vhe A']:= decomposition_connect_properties rfo sval adj cbtom
  bet_e oe.
have sublehe : {subset rcons (le :: sort (@edge_below _) (outgoing e)) he <=
                  all_edges open (e :: future_events)}.
  move=> x; rewrite mem_rcons inE => /orP[/eqP -> | ].
    by rewrite /all_edges; subset_tac.
  rewrite inE=> /orP[/eqP -> | ].
    by rewrite /all_edges; subset_tac.
  by apply: subo'.
have noc2:
   {in rcons (le :: sort (@edge_below _) (outgoing e)) he &, no_crossing R}.
  by move=> x y xin yin; apply: noc; apply: sublehe.
move=> x; rewrite !(mem_cat, inE) => /orP[xfc | ].
  by apply: lexPtW; apply: btom_left_corners; rewrite ocd; subset_tac.
rewrite orbA=> /orP[xin | xlc]; last first.
  apply: lexPtW.
  apply: btom_left_corners; rewrite ocd; subset_tac.
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

Lemma trial1 c1 c2 :
  below_alt (high c1) (low c2) ->
  open_cell_side_limit_ok c1 ->
  open_cell_side_limit_ok c2 ->
  valid_edge (high c1) (point e) ->
  valid_edge (low c2) (point e) ->
  pvert_y (point e) (high c1) < pvert_y (point e) (low c2) ->
  o_disjoint c1 c2.
Proof.
move=> noc12 ok1 ok2 vhc1 vlc2 cmpc1c2 q; apply/andP=>-[].
move=> /andP[]inc1 _ /andP[] inc2 /andP[] str2 _.
have /andP[_ vhc1q] := inside_open_cell_valid ok1 inc1.
have /andP[vlc2q _] := inside_open_cell_valid ok2 inc2.
move: (inc1)=> /andP[] /andP[] _ qh1 _.
have := transport_above_edge noc12 vhc1 vlc2 vhc1q vlc2q cmpc1c2 str2.
by rewrite qh1.
Qed.

Lemma trial2 c1 c2 :
  high c1 <| low c2 ->
  open_cell_side_limit_ok c1 ->
  open_cell_side_limit_ok c2 ->
  valid_edge (high c1) (point e) ->
  valid_edge (low c2) (point e) ->
  o_disjoint c1 c2.
Proof.
move=> c1bc2 ok1 ok2 v1 v2 q; apply/negP=> /andP[].
move=>/andP[] /andP[] /andP[] _ qbh1 /andP[] _ inx /andP[] _ stricterx.
have inx' : left_limit c1 < p_x q <= open_limit c1.
  by rewrite stricterx inx.
move: inx' {inx stricterx} => /(valid_high_limits ok1) vqhc1.
move=>/andP[] /andP[] _ /andP[] _ inx /andP[] qalc2 stricterx.
have inx' : left_limit c2 < p_x q <= open_limit c2.
  by rewrite stricterx inx.
move: inx' {inx stricterx} => /(valid_low_limits ok2) vqlc2.
rewrite (under_pvert_y vqlc2) -ltNge in qalc2.
rewrite (under_pvert_y vqhc1) in qbh1.
have /pvert_y_edge_below : pvert_y q (low c2) < pvert_y q (high c1).
  by apply: (lt_le_trans qalc2 qbh1).
by move=> /(_ vqlc2 vqhc1) /negP; apply.
Qed.

Lemma in_new_cell_not_in_first_old fc cc lcc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  {in [seq high c | c <- fc], forall g, p_x (point e) < p_x (right_pt g)} ->
  {in fc & opening_cells (point e) (outgoing e) le he,
     forall c1 c2, o_disjoint c1 c2}.
Proof.
move=> oe redges.
have [ocd [_ [_ [_ [_ [heq [leq [lein hein]]]]]]]] :=
   decomposition_main_properties oe exi.
have [pal puh vle vhe X] :=
  decomposition_connect_properties rfo sval adj cbtom bet_e oe.
set nc := opening_cells _ _ _ _.
set result_open :=  fc ++ nc ++ lc.
rewrite /nc/opening_cells; case oca_eq : opening_cells_aux => [s' c'].
have nceq : nc = rcons s' c' by rewrite /nc/opening_cells oca_eq.
have [nle nhe]:= higher_lower_equality oute oe nceq exi vle vhe.
rewrite head_rcons in nle; rewrite last_rcons in nhe.
have adj' : adjacent_cells result_open.
  rewrite /result_open/nc/opening_cells oca_eq.
  have oldnnil : rcons cc lcc != nil by apply/eqP/rcons_neq0.
  have newnnil : rcons s' c' != nil by apply/eqP/rcons_neq0.
  apply: (replacing_seq_adjacent oldnnil newnnil).
  - have := lower_edge_new_cells vle vhe.
    rewrite /opening_cells oca_eq=> /(_ _ erefl) /eqP ->.
    by rewrite head_rcons -leq.
  - have := higher_edge_new_cells oute vle vhe.
    rewrite /opening_cells oca_eq => /(_ _ erefl) /eqP ->.
    by rewrite last_rcons heq.
  - by rewrite -cats1 -!catA -ocd.
  by have := adjacent_opening' vle vhe oute; rewrite /opening_cells oca_eq.
have [fc0 | [fc' [lfc fceq]]] : fc = nil \/ exists fc' lfc, fc = rcons fc' lfc.
    by elim/last_ind : (fc) => [ | fc' lfc _];[left | right; exists fc', lfc].
  by rewrite fc0.
have lfceq : high lfc = le.
  have := last_first_cells_high cbtom adj bet_e oe; rewrite fceq.
  by rewrite map_rcons last_rcons.
set s1 := [seq high c | c <- fc'].
set s2 := [seq high c | c <- behead (rcons s' c') ++ lc].
set g2 := high (head c' s').
have roeq : [seq high c | c <- result_open] = s1 ++ [:: le, g2 & s2].
  rewrite /result_open nceq map_cat fceq -cats1 map_cat -catA /=.
  by congr (_ ++ (_ :: _)) => //; rewrite /g2 /s2 2!map_cat; case: (s').
have headin : head c' s' \in rcons s' c'.
  by rewrite -[X in _ \in X]cats1; subset_tac.
have val' : all (fun g => @valid_edge R g (point e)) (s1 ++ [:: le, g2 & s2]).
  apply/allP=> g; rewrite mem_cat=> /orP[/mapP[c cin ->] | ].
    apply/(seq_valid_high sval)/map_f.
    by rewrite ocd fceq cat_rcons; subset_tac.
  rewrite inE=> /orP[/eqP -> // | gnew].
    have [c cin ->] : exists2 c, c \in rcons s' c' ++ lc & g = high c.
      move: gnew; rewrite inE => /orP[gg2 | gs2].
      exists (head c' s');[ | by rewrite (eqP gg2)].
      by rewrite cat_rcons; subset_tac.
    move: gs2; rewrite /s2 map_cat mem_cat => /orP[].
      by move=> /mapP[c /behead_subset cin ->]; exists c=> //; subset_tac.
    by move=> /mapP[c cin ->]; exists c=> //; subset_tac.
  move: cin; rewrite mem_cat=> /orP[] cin; last first.
    by apply/(seq_valid_high sval)/map_f; rewrite ocd; subset_tac.
  have := opening_cells_subset vle vhe oute => /(_ c).
  rewrite -/nc nceq => /(_ cin)=> /andP[] _.
  rewrite /= inE => /orP[/eqP -> //| /oute it].
  by apply: valid_edge_extremities; rewrite it.
have noco : {in cell_edges open &, no_crossing R}.
  by apply: (sub_in2 _ noc); rewrite /all_edges; subset_tac.
have headccin : head lcc cc \in open by rewrite ocd; subset_tac.
have lein' : le \in all_edges open (e :: future_events).
  by rewrite /all_edges; subset_tac.
have hein' : he \in all_edges open (e :: future_events).
  by rewrite /all_edges; subset_tac.
have  [edgesabove edgesbelow noce]:=
   outgoing_conditions pal puh lein' hein' vle vhe subo noc oute.
have lbh : le <| he.
  apply: (edge_below_from_point_under _ vhe vle (underW puh) pal).
  by apply: noco; rewrite ?lein ?hein.
have rfr' : sorted (@edge_below R) (s1 ++ [:: le, g2 & s2]).
  have rfnew : s_right_form (opening_cells (point e) (outgoing e) le he).
      by apply: (opening_cells_right_form vle vhe (underWC pal) _ _ _ _ _ noce).
  have rfr : s_right_form result_open.
    rewrite /result_open /s_right_form !all_cat andbCA; apply/andP; split=> //.
    by rewrite -all_cat; apply: all_sub rfo; rewrite ocd; subset_tac.
  by have /path_sorted := seq_edge_below' adj' rfr; rewrite roeq.
set p' := Bpt (p_x (point e)) (pvert_y (point e) le).
have samex : p_x (point e) == p_x p' by apply: eqxx.
have vle' : valid_edge le p' by rewrite -(same_x_valid le samex).
have vg2 : valid_edge g2 (point e) by apply: (allP val'); subset_tac.
have vg2' : valid_edge g2 p' by rewrite -(same_x_valid _ samex).
have p'above : p' >>= le.
  by rewrite (strict_nonAunder vle') negb_and negbK (pvert_on vle).
have p'under : p' <<< g2.
  have := opening_cells_subset vle vhe oute; rewrite -/nc nceq => /(_ _ headin).
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
  by apply: (allP open_side_limit); rewrite ocd; subset_tac.
have outs':
   {in sort (@edge_below R) (outgoing e), forall g, left_pt g == (point e)}.
 by move: oute; apply: sub_in1=> g; rewrite mem_sort.
have c2ok : open_cell_side_limit_ok c2.
  have := opening_cells_side_limit vle vhe (underWC pal) puh oute.
  by rewrite -/nc nceq; move=> /allP/(_ c2 c2in).
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
    have := high_in_first_cells_below oe cbtom adj bet_e sval rfo noco redges.
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
  by apply: high_all_edges; rewrite ocd; subset_tac.
have := opening_cells_subset vle vhe oute.
rewrite -/nc nceq=> /(_ _ c2in) /andP[].
by rewrite inE=> /orP[/eqP -> | /subo //] _; rewrite lein'.
Qed.

Lemma middle_disj_last fc cc lcc lc nos lno:
 open = fc ++ cc ++ lcc :: lc ->
  adjacent_cells (fc ++ nos ++ lno :: lc) ->
  s_right_form  (fc ++ nos ++ lno :: lc)->
  low (head lno nos) =low (head lcc cc) ->
  high lno = high lcc ->
  {in [seq high c | c <- nos], forall g, left_pt g == (point e)} ->
  {in rcons nos lno &, disjoint_open_cells R} ->
   {in fc ++ nos ++ lno :: lc &, disjoint_open_cells R}.
Proof.
move=> ocd adjn rfon lecnct hecnct lefts ndisj.
Admitted.

Lemma opening_cells_aux_pairwise le he :
   point e >>> le ->
   point e <<< he ->
   le \in all_edges open (e :: future_events) ->
   he \in all_edges open (e :: future_events) ->
   valid_edge le (point e) ->
   valid_edge he (point e) ->
   pairwise (@edge_below _) 
         [seq high x | x <- (opening_cells (point e) (outgoing e) le he)].
Proof.
move=> pal puh lein hein vle vhe; rewrite /opening_cells.
case oca_eq : opening_cells_aux => [s c].
rewrite pairwise_map pairwise_rcons -pairwise_map /=.
have [_ it _]:= outgoing_conditions pal puh lein hein vle vhe subo' noc oute'.
have := opening_cells_aux_high vle vhe oute'; rewrite oca_eq /= => highsq.
 apply/andP; split.
  rewrite [X in is_true X]
     (_ : _ = all (fun x => x <| high c) [seq high x | x <- s]); last first.
    by rewrite all_map.
  have := opening_cells_aux_high_last vle vhe oute'; rewrite oca_eq /= => ->.
  by rewrite highsq; apply/allP.
rewrite highsq.
have loc_trans : {in sort (@edge_below _) (outgoing e) & &,
 transitive (@edge_below _)}.
  by apply: (@fan_edge_below_trans _ (point e)).
have /sort_edge_below_sorted : {in outgoing e &, no_crossing _}.
  by move=> x y xin yin; apply: noc; rewrite /all_edges/events_to_edges /=;
   rewrite !mem_cat ?xin ?yin ?orbT.
by rewrite (sorted_pairwise_in loc_trans (allss _)).
Qed.

Lemma new_edges_below_last_old fc cc lcc lc le:
  open = fc ++ cc ++ lcc :: lc ->
  all (fun x => valid_edge x(point e))
        [seq high x | x <- fc ++ cc ++ lcc :: lc] ->
  pairwise (@edge_below _) [seq high x | x <- fc ++ cc ++ lcc :: lc] ->
  point e >>= le ->
  point e <<< high lcc ->
  valid_edge le (point e) ->
  allrel (@edge_below _) 
    [seq high c | c <- 
      opening_cells (point e) (outgoing e) le (high lcc)]
        [seq high c | c <- lc].
Proof.
move=> ocd.
rewrite !map_cat !all_cat => /andP[] _ /andP[] _ /= /andP[] vhe vlc.
move=> + pal puh vle.
rewrite !pairwise_cat=> /andP[] _ /andP[] _ /andP[] _ /andP[] _.
rewrite /= => /andP[] heblc _.
rewrite /opening_cells.
case oca_eq : opening_cells_aux => [s c].
have := opening_cells_aux_high vle vhe oute'; rewrite oca_eq /= => highsq.
have := opening_cells_aux_high_last vle vhe oute'; rewrite oca_eq /= => highcq.
rewrite -cats1 allrel_mapl allrel_catl /= allrel_consl allrel0l ?andbT.
rewrite highcq heblc andbT.
rewrite -allrel_mapl highsq; apply/allrelP=> x y /[dup] xin xin' yin.
rewrite mem_sort in xin'.
have vx : valid_edge x (point e) by apply valid_edge_extremities; rewrite oute'.
have vy : valid_edge y (point e) by apply: (allP vlc).
have highlccley : high lcc <| y by apply: (allP heblc).
have puy : point e <<< y.
  by have := order_edges_strict_viz_point' vhe vy highlccley puh.
have pax : point e >>= x.
  rewrite -(eqP (oute' xin)); apply left_pt_above.
have nocxy : below_alt x y.
  apply: noc; rewrite /all_edges/events_to_edges /= ocd !mem_cat ?xin' ?orbT //.
  by rewrite !map_cat /= !mem_cat !inE yin !orbT.
by have := edge_below_from_point_above nocxy vx vy pax puy.
Qed.

Lemma new_edges_above_first_old fc cc lcc lc le:
  open = fc ++ cc ++ lcc :: lc ->
  all (fun x => valid_edge x(point e))
        [seq high x | x <- fc ++ cc ++ lcc :: lc] ->
  pairwise (@edge_below _) [seq high x | x <- fc ++ cc ++ lcc :: lc] ->
  all ((@edge_below _)^~ le) [seq high x | x <- fc] ->
  point e >>> le ->
  point e <<< high lcc ->
  valid_edge le (point e) ->
  allrel (@edge_below _) 
    [seq high c | c <- fc]
    [seq high c | c <- 
      opening_cells (point e) (outgoing e) le (high lcc)].
Proof.
move=> ocd.
rewrite !map_cat !all_cat => /andP[] vfc /andP[] _ /= /andP[] vhe _.
move=> + fcbl pal puh vle.
rewrite !pairwise_cat=> /andP[] fcbcc /andP[] _ /andP[] /=.
rewrite allrel_consr=> /andP[] pw' _ /andP[] pw _.
rewrite /opening_cells.
case oca_eq : opening_cells_aux => [s c].
have := opening_cells_aux_high vle vhe oute'; rewrite oca_eq /= => highsq.
have := opening_cells_aux_high_last vle vhe oute'; rewrite oca_eq /= => highcq.
rewrite -cats1 map_cat allrel_catr allrel_consr /=.
have -> : all ((@edge_below _)^~ (high c)) [seq high x | x <- fc].
  rewrite highcq; move: fcbcc; rewrite allrel_catr allrel_consr.
  by move=> /andP[] _ /andP[].
rewrite allrel0r.
have -> //: allrel (@edge_below _) [seq high x | x <- fc] [seq high y | y <- s].
rewrite highsq.
apply/allrelP=> x y xin yin.
have vx : valid_edge x (point e) by apply: (allP vfc).
have vy : valid_edge y (point e).
  by apply: valid_edge_extremities; rewrite oute'.
have puy : point e <<= y.
  by rewrite -(eqP (oute' yin)); apply: left_pt_below.
have xble : x <| le by apply: (allP fcbl).
have pax : point e >>> x.
  apply/negP=> pux; case/negP: pal.
  by apply: (order_edges_viz_point' vx vle xble pux).
have nocyx : below_alt y x.
  apply: noc; rewrite ocd /all_edges/events_to_edges; last first.
    by rewrite !(cell_edges_cat, mem_cat) ?xin ?orbT //.
  rewrite /= mem_cat [X in (_ || X)]mem_cat.
  by rewrite mem_sort in yin; rewrite yin !orbT.
by have := edge_below_from_point_under nocyx vy vx puy pax.
Qed.

Lemma in_new_cell_not_in_last_old fc cc lcc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  {in opening_cells (point e) (outgoing e) le he & lc,
     forall c1 c2, o_disjoint c1 c2}.
Proof.
move=> oe.
have [ocd [_ [_ [_ [_ [heq [leq [lein hein]]]]]]]] :=
  decomposition_main_properties oe exi.
have [pal puh vle vhe allnct] :=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe.
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
    higher_lower_equality oute oe erefl exi vle vhe.
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
  by rewrite /all_edges; subset_tac.
have hein' : he \in all_edges open (e :: future_events).
  by rewrite /all_edges; subset_tac.
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
  by apply: (allP rfo); rewrite ocd lceq'; subset_tac.
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
  by rewrite ocd lceq'; subset_tac.
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
        have lelow := decomposition_under_low_lc oe cbtom adj bet_e rfo sval.
        have adjlc' : adjacent_cells (lcc :: lc).
          move: adj; rewrite ocd => /adjacent_catW[] _.
          by move=> /adjacent_catW[] _.
        have := seq_low_high_shift.
        move=> /(_ (lcc :: lc) isT adjlc') /= => - [] tmp.
        move=> g; rewrite inE => /orP[/eqP -> | ].
          have lcco : lcc \in open by rewrite ocd; subset_tac.
          have := allP gs (high lcc) (map_f _ lcco); rewrite /edge_side_prop.
          by rewrite -heq vhe ltNge le_eqVlt orbC lt1 /=.
        move: tmp; set s5 := rcons _ _ => tmp gin.
        have : g \in s5 by rewrite tmp; subset_tac.
        rewrite /s5 mem_rcons inE orbC=> /orP[/mapP[c' c'in gc'] | ].
          have vc' : valid_edge (low c') (point e).
            by apply/(seq_valid_low sval)/map_f; rewrite ocd; subset_tac.
          have := lelow _ c'in; rewrite strict_under_pvert_y // => ga.
          move: gin=> /mapP[c'' c''in gc''].
          have c''o : c'' \in open by rewrite ocd; subset_tac.
          have := allP gs (high c'') (map_f _ c''o); rewrite /edge_side_prop.
          rewrite (seq_valid_high sval); last by apply/map_f.
          by rewrite -gc'' gc' ltNge le_eqVlt ga orbT /=.
        move: cbtom=> /andP[] _; rewrite ocd !last_cat /= => /eqP -> /eqP ->.
        by move: inbox_e=> /andP[] _ /andP[] _ /andP[] + _.
(* finished proving all_left *)
      have noc' : {in he :: [seq high i | i <- lc] &, no_crossing R}.
        apply: sub_in2 noc.
        move=> g; rewrite inE => /orP[/eqP -> // | /mapP[c cin ->]].
        by apply: high_all_edges; rewrite ocd; subset_tac.
      have sval' : {in he :: [seq high i | i <- lc], forall g,
                   valid_edge g (point e)}.
        move=> g; rewrite inE=> /orP[/eqP ->// | /mapP[c' c'in gc']].
        rewrite gc'; apply/(seq_valid_high sval)/map_f.
        by rewrite ocd; subset_tac.
      by have := edge_below_trans (or_intror all_left) sval' noc'.
    have adj2 : adjacent_cells (last c1 s2 :: rcons s3 c2).
      move: adj'; rewrite /result_open => /adjacent_catW[] _.
      rewrite /new_cells /opening_cells oca_eq nceq' -catA /= => /adjacent_catW[] _.
      by rewrite /= cat_path lceq' cat_path => /andP[] _ /andP[] +.
      have := seq_edge_below' adj2 rf' => /= /andP[] _.
      rewrite (path_sorted_inE treblc); last first.
      apply/allP=> g; rewrite hs2 !inE => /orP[/eqP -> | /mapP[c cin ->]].
        by rewrite topredE inE eqxx.
      by rewrite topredE inE lceq' map_f ?orbT //; subset_tac.
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
    by rewrite low_all_edges // ocd; subset_tac.
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
    by apply/map_f; rewrite ocd; subset_tac.
  by rewrite abs => /(_ isT isT).
move=> pp; apply/negP=> /andP[] sio1 sio2.
have lho_sub : {subset le :: he :: outgoing e <=
                     all_edges open (e :: future_events)}.
  move=> g; rewrite !inE =>/orP[/eqP -> // | /orP[/eqP -> // | ]].
  by apply: subo.
have vp1 : valid_edge (high c1) pp.
  apply: valid_high_limits.
    apply: (allP (opening_cells_side_limit vle vhe (underWC pal) puh oute)).  
    by rewrite /opening_cells oca_eq.
by move: sio1=> /andP[] /andP[] _ /andP[] _ -> /andP[] _ ->.
have vp2 : valid_edge (low c2) pp.
  apply: valid_low_limits.
    by apply: (allP open_side_limit); rewrite ocd; subset_tac.
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
  := decomposition_main_properties oe exi.
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
    have lccino : lcc \in open by rewrite ocd; subset_tac.
    have [ _ uhe _ _ nctn]:= decomposition_connect_properties rfo sval adj
         cbtom bet_e oe.
    apply: (last_cells_edge_side futq) => //.
    by rewrite -heq.
  rewrite mem_cat=> /orP[infc | inlc].
    have cino : c \in open by rewrite ocd; subset_tac.
    apply: (first_cells_edge_side futq) => //.
    by apply: (decomposition_above_high_fc oe cbtom adj bet_e rfo sval infc).
  have cino : c \in open by rewrite ocd; subset_tac.
  have [vlc vhc] :
     valid_edge (low c) (point e) /\ valid_edge (high c) (point e).
    by apply/andP; apply: (allP sval _ cino).
  suff/(last_cells_edge_side futq cino): point e <<< high c by [].
  apply: (order_edges_strict_viz_point' vlc vhc (allP rfo _ cino)).
  by apply: (decomposition_under_low_lc oe cbtom adj bet_e rfo sval inlc).
have common' : all [pred x | edge_side_prop e' (high x)] (lcc :: fc ++ lc).
  by apply/allP=> c cin; apply: common.
rewrite all_map all_cat /= all_cat !andbA andbC !andbA -andbA.
apply/andP; split.
  by rewrite -all_cat; apply: all_sub common'; subset_tac.
rewrite andbC.
rewrite -[_ && _]/(all [pred x | edge_side_prop e' (high x)] [:: lno & nos]).
apply/allP=> c cinn.
have := opening_cells_aux_subset vle vhe (outleft_event_sort oute) oca_eq.
move=> /(_ c); rewrite mem_rcons cinn=> /(_ isT) /andP[] _.
rewrite /= inE=> /orP[/eqP ishe | ].
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
case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
  move=> -[] <- <-.
  have := opening_cells_aux_high vlo vho (outleft_event_sort oute).
  rewrite ogq oca_eq /= => abs.
  by have := size_sort (@edge_below _) (g1 :: gl); rewrite -abs.
move=> -[] <- <-.
have := opening_cells_aux_high vlo vho (outleft_event_sort oute).
rewrite ogq oca_eq /= => highs.
have -> : high lno = high lsto.
  have := opening_cells_aux_high_last vlo vho (outleft_event_sort oute).
  by rewrite ogq oca_eq /=.
rewrite case_lsto /=.
apply/andP; split.
  apply: (outgoing_edge_side_prop futq).
  by rewrite ogq -(mem_sort (@edge_below _)) -highs inE eqxx.
apply/allP=> g gin; apply: (outgoing_edge_side_prop futq).
by rewrite ogq -(mem_sort (@edge_below _)) -highs inE gin orbT.
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
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  case uocq : update_open_cell => [lnop lno].
  rewrite /state_open_seq /=.
  move=> clae'.
  rewrite -catA -cat_rcons; apply/allP=> g /mapP [c + gq].
  rewrite !mem_cat => /orP[cinfop | ].
    rewrite gq.
    have cino : c \in open by rewrite /open; subset_tac.
    apply: (first_cells_edge_side futq) => //.
    have [lop' [lfop fopq]] : exists fop' lfop, fop = rcons fop' lfop.
      by elim/last_ind : (fop) cinfop => [ | fc' lfc _];[ | exists fc', lfc].
    have hlfop : high lfop = low lsto.
      move: adj; rewrite /open fopq cat_rcons=> /adjacent_catW[] _.
      by rewrite /= => /andP[] /eqP.
    have svalf : seq_valid fop (point e).
      by apply/allP=> c' c'in; apply: (allP sval); rewrite /open; subset_tac.
    have adjf : adjacent_cells fop by move: adj=> /adjacent_catW[].
    have rff : s_right_form fop.
      by apply/allP=> c' c'in; apply: (allP rfo); rewrite /open; subset_tac.
    have abf : point e >>> high (last dummy_cell fop).
      by rewrite fopq last_rcons hlfop.
    by have [ _ /(_ _ cinfop)]:= above_all_cells svalf adjf rff abf.
  move=>/orP[ | cinlop]; last first.
    have cino : c \in open by rewrite /open; subset_tac.
    rewrite gq; apply: (last_cells_edge_side futq) => //.
    case lopq : lop (cinlop) => [ // | flop lop'] _.
    have lflop : low flop = high lsto.
      by move: adj; rewrite /open lopq=> /adjacent_catW[] _ /andP[]/eqP.
    have svall : seq_valid lop (point e).
      by apply/allP=> c' c'in; apply: (allP sval); rewrite /open; subset_tac.
    have adjl : adjacent_cells lop.
      by move: adj; rewrite /open -cat_rcons=> /adjacent_catW[].
    have rfl : s_right_form lop.
      by apply: all_sub rfo; rewrite /open; subset_tac.
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
  decomposition_main_properties oe' exi2.
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite oe' => oe.
have [ocd [_ [_ [fopfc'nct _]]]] := decomposition_main_properties oe exi.
have [_ ebellcc _ _ _] := decomposition_connect_properties rfo sval adj cbtom
  bet_e oe.
(*have [_ ebellcc _ _ _] := connect_properties cbtom adj rfo sval
  bet_e ocd fopfc'nct ctns ctn flcnct. *)
case ogq : (outgoing e) => [ | og1 ogs] /=.
  rewrite cats0; set nop := Bcell _ _ _ _ => clae'.
  apply/allP=> g /mapP [c + ->].
  rewrite mem_cat inE orbCA=> /orP[/eqP -> | ]; last first.
    move=>/orP[] cin.
(* TODO : big duplication here (use of below_all_cells) *)
      have cino : c \in open by rewrite /open ocd; subset_tac.
      apply: (first_cells_edge_side futq) => //.
      by have := decomposition_above_high_fc oe cbtom adj bet_e rfo sval cin.
    have lcsub: {subset lc <= open}.
      by rewrite /open ocd; subset_tac.
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
      by rewrite -lfcq -heq.
    by have /(_ _ cin):= below_all_cells svall adjl rfl bel.
  rewrite /= heq.
  apply: (last_cells_edge_side futq).
    rewrite /open ocd; subset_tac.
  by rewrite -heq.
rewrite -ogq /=.
case oca_eq : (opening_cells_aux _ _ _ _) => [nops lnop] /=.
have hein' : he \in cell_edges open.
  by rewrite /open cell_edges_cat; subset_tac.
move=> clae'.
have := step_keeps_edge_side_default; rewrite oe.
have inlsto : contains_point (point e) lsto.
  rewrite /contains_point  -leNgt ltW; last first.
    by rewrite ltNge; exact: palstol.
  by move: ebelow=> /negbFE; rewrite lstheq.
have [fc'0 lelsto]  : fc' = [::] /\ le = low lsto.
  by have := last_step_situation oe' pxhere (negbT eonlsthe) (negbFE ebelow).
rewrite lelsto oca_eq /= /state_open_seq /= =>
  /(_ nil dummy_cell dummy_edge 0).
move: clae'; case nopsq : nops => [ | c0 l0] /=; rewrite ?cats0=> clae'.
  by rewrite futq; apply.
have := step_keeps_invariant1; rewrite /invariant1/state_open_seq /=.
rewrite pxhere eqxx /= ebelow eonlsthe oe' /update_open_cell_top oca_eq ogq.
rewrite nopsq /= catA -(catA (fop ++ fc')) /= inv1_seq_set_left_pts.
move=>[] clae2 _ /(_ clae2).
rewrite /edge_side; rewrite futq !map_cat /= !map_cat /= !all_cat /= !all_cat.
by move=> /andP[] /andP[] -> /= /andP[] -> -> ->.
Qed.

Lemma inside_box_sorted_le :
  sorted <=%R [seq pvert_y (point e) (high c) | c <- extra_bot :: open].
Proof.
have adj' : adjacent_cells (extra_bot :: open).
  rewrite /=; move: cbtom=> /andP[] /andP[]; case: (open) adj => // o1 os + _.
  by move=> /= -> /eqP ->; rewrite eqxx.
apply adjacent_right_form_sorted_le_y => //=.
  rewrite andbb; apply/andP; split=> //.
  by apply: (inside_box_valid_bottom_top inbox_e)=> //; rewrite inE eqxx.
by rewrite edge_below_refl.
Qed.

Lemma head_cat [T : eqType] (s1 s2 : seq T) (a : T):
   s1 != nil -> head a (s1 ++ s2) = head a s1.
Proof. by case : s1 => [ | b s1]. Qed.

Lemma first_cells_strictly_below_event fc cc lcc lc le he:
open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
(fc != [::] -> high (last dummy_cell fc) = le) ->
(fc != [::] -> low (head dummy_cell fc) = bottom) ->
{in cell_edges fc, forall g, pvert_y (point e) g < p_y (point e)}.
Proof.
move=> oe higfc lfcbot.
have := decomposition_main_properties oe exi.
move=> [ocd _].
have [pal _ vle _ _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe.
suff highs : {in [seq high c | c <- fc],
               forall g, pvert_y (point e) g < p_y (point e)}.
  move=> g; rewrite mem_cat=>/orP[] gin; last by apply: highs.
  have fcn0 : fc != nil by move: gin; case: (fc).
  have : g \in rcons [seq low c| c <- fc] le.
    by rewrite mem_rcons inE gin orbT.
  rewrite - (higfc fcn0).
  rewrite seq_low_high_shift //; last first.
    by move: (adj); rewrite ocd=> /adjacent_catW[].
  rewrite inE=> /orP[/eqP -> | ]; last by apply: highs.
  rewrite lfcbot // ltNge -under_pvert_y.
    by move: bet_e=> /andP[].
  by rewrite /valid_edge !ltW; move: inbox_e=> /andP[] _ /andP[] /andP[].
have /= pathlt : sorted <=%R [seq pvert_y (point e) (high c) 
                               | c <- extra_bot :: open].
  by apply: inside_box_sorted_le.
move=> g /mapP[c cin gceq].
have [s1 [s2 fceq]] := mem_seq_split cin.
have vertle : pvert_y (point e) le < p_y (point e).
  by move: pal; rewrite under_pvert_y // ltNge.
have := decomposition_above_high_fc oe cbtom adj bet_e rfo sval cin.
rewrite under_pvert_y ?ltNge ? gceq // (seq_valid_high sval) // map_f //.
by rewrite ocd fceq; subset_tac.
Qed.

Lemma first_cell_high_edges_right fc cc lcc lc nos lno:
  open = fc ++ cc ++ lcc :: lc ->
  close_alive_edges (fc ++ nos ++ lno :: lc) future_events ->
  {in cell_edges fc , forall g, pvert_y (point e) g < p_y (point e)} ->
  {in [seq high c | c <- fc], forall g, p_x (point e) < p_x (right_pt g)}.
Proof.
(* TODO : This easy proof indicates that edge_side_prop could be made
  much easier, only the top part being important. *)
move=> ocd clae_new lowvert.
have fcopen : {subset fc <= open} by rewrite ocd; subset_tac.
have valhfc : {in [seq high c | c <- fc], forall g, valid_edge g (point e)}.
  by move=> g /mapP[c cin ->]; apply: proj2 (andP (allP sval _ (fcopen _ _))).
have clae' : close_alive_edges fc future_events.
  by apply: all_sub clae_new; subset_tac.
move=> g gin.
  have /orP[bottop | ] : end_edge g future_events.
      by move: gin=> /mapP[c cin ->]; move: (allP clae' _ cin)=>/andP[].
    move: inbox_e => /andP[] _ /andP[] /andP[] _ + /andP[] _.
    by move: bottop; rewrite !inE=> /orP[] /eqP ->.
  move=> /hasP [e' e'in /eqP /[dup]geq ->].
  have : lexPt (point e) (point e').
     have := sort_evs; rewrite (path_sortedE (@lexPtEv_trans _))=>/andP[] + _.
     by move=> /allP /(_ e' e'in).
  move=>/orP[ // | ] /andP[] /eqP xs ys.
  suff /eqP abs : pvert_y (point e) g == p_y (point e').
    have:= lowvert g; rewrite mem_cat gin orbT abs =>/(_ isT).
    by rewrite ltNge le_eqVlt ys orbT.
  have vg : valid_edge g (point e) by apply: valhfc.
  have := pvert_on vg => ievg.
  move: (right_on_edge g); rewrite geq => ev'g.
  by apply: (on_edge_same_point ievg ev'g) => /=; rewrite xs eqxx.
Qed.

Lemma first_cell_edges_below fc cc lcc lc le:
  open = fc ++ cc ++ lcc :: lc ->
  (fc != [::] -> high (last dummy_cell fc) = le) ->
  (fc != [::] -> low (head dummy_cell fc) = bottom) ->
  {in [seq high c | c <- fc], forall g, p_x (point e) < p_x (right_pt g)} ->
  {in cell_edges fc, forall g, g <| le}.
Proof.
set fc_edges := cell_edges fc.
move=> ocd higfc lfcbot fchright.
have fcopen : {subset fc <= open} by rewrite ocd; subset_tac.
have valhfc : {in [seq high c | c <- fc], forall g, valid_edge g (point e)}.
  by move=> g /mapP[c cin ->]; apply: proj2 (andP (allP sval _ (fcopen _ _))).
have noc3 : {in [seq high c | c <- fc] &, no_crossing R}.
  move: noc; apply: sub_in2=> ? /mapP[c cin ->]; apply: high_all_edges.
  by rewrite ocd; subset_tac.
have tr : {in [seq high c | c <- fc]  & &, transitive (@edge_below R)}.
  by apply: (edge_below_trans _ valhfc) => //; left.
(* TODO: remove duplication with "suff highs" in first_cells_strictly_bel.. *)
suff highs : {in [seq high c | c <- fc], forall g, g <| le}.
  move=> g; rewrite mem_cat=>/orP[] gin; last by apply: highs.
  have fcn0 : fc != nil by move: gin; case: (fc).
  have : g \in rcons [seq low c| c <- fc] le by rewrite -cats1; subset_tac.
  rewrite -higfc //.
  rewrite seq_low_high_shift //; last first.
    by move: (adj); rewrite ocd=> /adjacent_catW[].
  rewrite inE=> /orP[/eqP -> | inh ]; last by rewrite higfc // highs.
  rewrite (lfcbot fcn0).
  apply: bottom_edge_below.
  rewrite ocd mem_cat map_f ?orbT // mem_cat.
  by case: (fc) fcn0 => // c0 fc'; rewrite last_cons mem_last.
move=> g gin.
have fcn0 : fc != nil by move: gin; case: (fc).
have sfcgt0 : (0 < size fc)%N by rewrite lt0n size_eq0.
have := seq_edge_below' adj rfo.
rewrite [X in head _ (map _ X)]ocd -nth0.
rewrite (nth_map dummy_cell _ (@low R) _); last first.
  by rewrite size_cat addn_gt0 sfcgt0.
rewrite ocd map_cat cat_path nth0 head_cat // => /andP[] + _.
move: gin=> /mapP[c cin geq].
have [fch [fct ]] := mem_seq_split cin.
rewrite -[_ :: _]/([:: _] ++ _) catA cats1 => fcteq.
rewrite fcteq !map_cat cat_path map_rcons last_rcons=> /andP[] _.
have <- := higfc fcn0.
rewrite (path_sorted_inE tr); last first.
  by apply/allP=> ? ?; rewrite topredE fcteq cat_rcons map_cat /=; subset_tac.
case fcteq' : fct => [ | fct0 fct'].
  by rewrite fcteq fcteq' cats0 last_rcons geq edge_below_refl.
move=> /andP[] /allP /(_ (high (last dummy_cell fc))) + _.
rewrite geq; apply.
by rewrite fcteq -fcteq' map_f // fcteq' last_cat /= mem_last.
Qed.

Lemma head_rcons [A : Type](def : A) (s : seq A) (a : A) :
  head def (rcons s a) = head a s.
Proof. by case: s. Qed.

Lemma disjoint_open_parts fc cc lcc lc nos lno :
   open = fc ++ cc ++ lcc :: lc ->
  close_alive_edges (fc ++ nos ++ lno :: lc) future_events ->
  low (head lcc cc) <| high lcc ->
   low (head lcc cc) = low (head lno nos) ->
   high lcc = high lno ->
  {in rcons nos lno &, disjoint_open_cells R} ->
  {in fc ++ nos ++ lno :: lc &, disjoint_open_cells R}.
Proof.
move=> ocd clae_new low_high.
have lfcbot : fc != [::] -> low (head dummy_cell fc) = bottom.
  move: cbtom; rewrite ocd.
  by case: (fc) => [// | /= ca ?] /andP[] /andP[] _ /=/eqP.
have higfc : fc != nil -> high (last dummy_cell fc) = low (head lcc cc).
  elim/last_ind : (fc) ocd => [// |s c' _] /= ocd.
  move: adj; rewrite ocd cat_rcons last_rcons =>/adjacent_catW[] _ /=.
  by case: (cc) => [ | cc0 cc'] /= /andP[] /eqP ->.
move=> le_cnct.
move=> he_cnct.
have adjnew : adjacent_cells (fc ++ nos ++ lno :: lc).
  rewrite (_ : fc ++ nos ++ lno :: lc = fc ++ (rcons nos lno) ++ lc);last first.
    by rewrite -cats1 -!catA.
  admit.
have rfnew : s_right_form (fc ++ nos ++ lno :: lc).
  admit.
apply: (@middle_disj_last _ cc lcc)=> //.
Admitted.

Lemma pairwise_subst {T : Type} [leT : rel T] (os ns s1 s2 : seq T) :
  pairwise leT (s1 ++ os ++ s2) ->
  pairwise leT ns ->
  allrel leT s1 ns ->
  allrel leT ns s2 ->
  pairwise leT (s1 ++ ns ++ s2).
Proof.
rewrite !pairwise_cat !allrel_catr => /andP[] /andP[] _ -> /andP[] ->.
by move=>/andP[] _ /andP[] _ -> -> -> ->.
Qed.

Lemma pairwise_subst1 {T : eqType} [leT : rel T] (oc nc : T)(s1 s2 : seq T) :
  leT nc =1 leT oc -> leT^~ nc =1 leT^~ oc ->
  pairwise leT (s1 ++ oc :: s2) = pairwise leT (s1 ++ nc :: s2).
Proof.
move=> l r.
by rewrite !(pairwise_cat, pairwise_cons, allrel_consr) (eq_all l) (eq_all r).
Qed.

Lemma step_keeps_pw_default :
  let '(fc, cc, lcc, lc, le, he) :=
  open_cells_decomposition open (point e) in
  let '(nos, lno) := 
    opening_cells_aux (point e)
        (sort (@edge_below _) (outgoing e)) le he in
    pairwise (@edge_below _) [seq high x | x <- fc ++ nos ++ lno :: lc].
(*    {in (fc ++ nos ++ lno :: lc) &, disjoint_open_cells R}. *)
Proof.
case oe: (open_cells_decomposition open (point e)) =>
  [[[[[fc cc] lcc] lc] le] he].
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]]
  := decomposition_main_properties oe exi.
have [pal puh vle vhe allnct] :=
  decomposition_connect_properties rfo sval adj cbtom bet_e oe.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
have oc_eq : opening_cells (point e) (outgoing e) le he = rcons nos lno.
  by rewrite /opening_cells oca_eq.
rewrite -cat_rcons.
rewrite pairwise_map.
move: pwo; rewrite pairwise_cons ocd -cat_rcons pairwise_map=> /andP[] _ pwo'.
have vhocd : all ((@valid_edge _)^~ (point e))
     [seq high x | x <- fc ++ cc ++ lcc :: lc].
  by rewrite -ocd; apply/allP; apply: seq_valid_high.
move: (pwo'); rewrite cat_rcons -pairwise_map=> pwo2.
have puh' : point e <<< high lcc by rewrite -heq.
apply: (pairwise_subst pwo'); rewrite -?pairwise_map.
- rewrite -oc_eq.
  have lein' : le \in all_edges open (e :: future_events).
    by rewrite mem_cat lein.
  have hein' : he \in all_edges open (e :: future_events).
    by rewrite mem_cat hein.
  by apply: opening_cells_aux_pairwise.
- have : allrel (@edge_below _) [seq high x | x <- fc]
          [seq high x | x <- rcons nos lno].
    have fcle : all ((@edge_below _)^~ le) [seq high x | x <- fc].
      apply/allP=> x /mapP[xc xcin xq].
      elim/last_ind : {-1} (fc) (erefl fc) => [ | fc' lfc _] fcq.
        by move: xcin; rewrite fcq.
      have := last_first_cells_high cbtom adj bet_e oe => <-.
      rewrite fcq map_rcons last_rcons xq.
      move: xcin; rewrite fcq mem_rcons inE=> /orP[/eqP -> | xcin ].
        by apply: edge_below_refl.
      move: pwo'; rewrite pairwise_cat fcq pairwise_rcons=> /andP[] _ /andP[].
      by move=> /andP[] + _ _ => /allP /(_ xc xcin) /=.
    have := new_edges_above_first_old ocd vhocd pwo2 fcle pal puh' vle.
    by rewrite -oc_eq heq.
  by rewrite allrel_mapr allrel_mapl.
have : allrel (@edge_below _) [seq high x | x <- rcons nos lno]
            [seq high x | x <- lc].
   have := new_edges_below_last_old ocd vhocd pwo2 (underWC pal) puh' vle.
   by rewrite -heq oc_eq.
by rewrite allrel_mapl allrel_mapr.
Qed.

Lemma step_keeps_disjoint_open_default :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) :=
      opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
  {in (fc ++ nos ++ lno :: lc) &, disjoint_open_cells R}.
Proof.
case oe: (open_cells_decomposition open (point e)) =>
  [[[[[fc cc] lcc] lc] le] he].

have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]]
  := decomposition_main_properties oe exi.
have [pal puh vle vhe allnct] :=
  decomposition_connect_properties rfo sval adj cbtom bet_e oe.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
have adjnew : adjacent_cells (fc ++ nos ++ lno :: lc).
  rewrite -cat_rcons.
  have cclccn0 : rcons cc lcc != nil by apply /eqP/rcons_neq0.
  have noslnon0 : rcons nos lno != nil by apply/eqP/rcons_neq0.
  have [adjn lle] : adjacent_cells (rcons nos lno) /\
              low (head dummy_cell (rcons nos lno)) = le.
    by apply: (adjacent_opening_aux' vle vhe oute' oca_eq).
  have lnlo : low (head dummy_cell (rcons cc lcc)) =
              low (head dummy_cell (rcons nos lno)).
    by rewrite lle; rewrite head_rcons.
  have hnho : high (last dummy_cell (rcons cc lcc)) =
        high (last dummy_cell (rcons nos lno)).
    rewrite !last_rcons -heq.
    have := opening_cells_aux_high_last vle vhe oute'.
    by rewrite oca_eq /=.
  have adjocd : adjacent_cells (fc ++ rcons cc lcc ++ lc).
    by rewrite cat_rcons -ocd.
  by apply (replacing_seq_adjacent cclccn0).
have oc_eq : opening_cells (point e) (outgoing e) le he = rcons nos lno.
  by rewrite /opening_cells oca_eq.
have newok : all open_cell_side_limit_ok (fc ++ nos ++ lno :: lc).
  rewrite -cat_rcons -oc_eq !all_cat.
  move: open_side_limit; rewrite ocd -cat_rcons !all_cat=> /andP[] ->.
  move=> /andP[] _ ->; rewrite /= andbT.
  by apply opening_cells_side_limit=> //; apply/underWC.
apply: disoc=> //.
by have := step_keeps_pw_default; rewrite oe oca_eq.
Qed.

Lemma step_keeps_pw :
  pairwise (@edge_below _)
     [seq high x | x <- state_open_seq (step e (Bscan fop lsto lop cls lstc
           lsthe lstx))].
Proof.
rewrite /step/=.
case: ifP=> [pxaway | /negbFE/eqP/[dup] pxhere/abovelstle palstol].
  case oe : (open_cells_decomposition (fop ++ lsto :: lop) (point e))=>
    [[[[[fc cc] lcc] lc] le] he].
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
move: step_keeps_pw_default; rewrite /open.
  by rewrite oe oca_eq /state_open_seq /= catA.
case: ifP=> [eabove | ebelow].
  case oe: (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  have := step_keeps_pw_default; rewrite oe' oca_eq.
  rewrite [state_open_seq _]
           (_ : _ = (rcons fop lsto ++ fc') ++ nos ++ lno :: lc); last first.
    by rewrite /state_open_seq /= cat_rcons !catA.
  by apply.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  rewrite /state_open_seq /=.
  rewrite /update_open_cell.
  case oq : (outgoing e) => [ | fog ogs] /=.
    rewrite cats0 map_cat /=.
    move: pwo; rewrite pairwise_cons /open => /andP[] _.
    by rewrite map_cat /=.
  have ocd : open_cells_decomposition open (point e) =
          (fop, [::], lsto, lop, low lsto, high lsto).
    by rewrite open_cells_decomposition_single; rewrite // -lstheq.
  have same_left cg lpts : (fun c' => (edge_below (high cg) (high c'))) =1
      (fun c' => (edge_below (high (set_left_pts cg lpts))(high c'))).
    by move=> c'; rewrite /set_left_pts /=.
  have same_right cg lpts : (fun c' => edge_below (high c') (high cg)) =1
      (fun c' => edge_below (high c') (high (set_left_pts cg lpts))).
    by move=> c'; rewrite /set_left_pts /=.
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | f s] c] /=.
    rewrite cats0 -cat_rcons.
    have:= step_keeps_pw_default.
    rewrite ocd oq oca_eq /= cat_rcons !pairwise_map => pw.
    have onn : outgoing e != [::] by rewrite oq.
    have := opening_cells_aux_absurd_case vlo vho onn oute.
    by rewrite oq oca_eq.
  have := step_keeps_pw_default.
  rewrite ocd oq oca_eq /= !pairwise_map => pw.
  rewrite -catA /=.
  have := @pairwise_subst1 _
                 (fun c1 c2 => edge_below (high c1) (high c2)) f
      (set_left_pts f [:: point e & behead (left_pts lsto)]
) fop (s ++ c :: lop)
      (same_left f (point e :: behead (left_pts lsto)))
      (same_right f (point e :: behead (left_pts lsto))) => <-.
  exact: pw.
(* Now the point is on lsthe *)
(* Next12 lines duplicated from the end of step_keeps_invariant1 *)
have lsto_ctn : contains_point'(point e) lsto.
  by rewrite /contains_point' -lstheq (negbFE ebelow) abovelstle.
have exi2 : exists2 c, c \in (lsto :: lop) & contains_point' (point e) c.
  by exists lsto; rewrite // inE eqxx.
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
  rewrite oe => oe'.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
  decomposition_main_properties oe' exi.
have [ocd' _] := decomposition_main_properties oe exi2.
have [fc'0  lelsto] : fc' = [::] /\ le = low lsto.
  by have := last_step_situation oe pxhere (negbT eonlsthe) (negbFE ebelow).
rewrite /update_open_cell_top.
case o_eq : (outgoing e) => [ | g l]; rewrite -?o_eq; last first.
(* If there are outgoing edges, this cell is treated as in the default case. *)
  have := step_keeps_pw_default; rewrite oe' -lelsto.
  case: (opening_cells_aux _ _ _ _) => [nos lno].
  case nosq : nos => [ | fno nos'] /=.
    by rewrite /state_open_seq /= !cats0.
  rewrite /state_open_seq /= catA -(catA (_ ++ _)) /= map_cat /= => it.
  by rewrite map_cat /=.
have := step_keeps_pw_default; rewrite oe' -lelsto o_eq /=.
have vle : valid_edge le (point e) by apply: open_edge_valid.
have vhe : valid_edge he (point e) by apply: open_edge_valid.
by rewrite pvertE // pvertE //= !map_cat /= cats0.
Qed.

Lemma opening_cells_last_left_pts le he :
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  outgoing e != nil ->
  point e <<< he ->
  left_pts (opening_cells_aux (point e) (sort (@edge_below _) (outgoing e))
     le he).2
 = Bpt (p_x (point e)) (pvert_y (point e) he) :: point e :: nil.
Proof.
move=> vle vhe onn puh.
have puh' : p_y (point e) < pvert_y (point e) he.
  by rewrite -strict_under_pvert_y.
have pdif :{| p_x := p_x (point e); p_y := pvert_y (point e) he |} != point e.
  rewrite pt_eqE negb_and /=; apply/orP; right; rewrite eq_sym.
  by move: puh'; rewrite lt_neqAle => /andP[] ->.
case ogeq : (sort _ (outgoing e)) (mem_sort (@edge_below _) (outgoing e)) =>
  [ | fog ogs] // .
  move=> abs; case ogeq' : (outgoing e) onn => [ | f q] //=.
  by suff : f \in [::];[rewrite in_nil | rewrite abs ogeq' inE eqxx].
move=> elems.
have lf : left_pt fog = point e.
  by move: oute'; rewrite ogeq=> oute2; apply/eqP/oute2; rewrite inE eqxx.
have vf : valid_edge fog (point e) by rewrite valid_edge_extremities // lf eqxx.
rewrite /= pvertE //.
have : {subset ogs <= outgoing e} by move=> x xin; rewrite -elems inE xin orbT.
move: (fog) lf vf {ogeq elems}.
elim : (ogs) le {vle} => [ | f q Ih] //= => le fog1 lfog1 vf1 qsubo.
  rewrite pvertE // pvertE //= (negbTE pdif).
  have -> : pvert_y (point e) fog1 = p_y (point e).
     by apply on_pvert; rewrite -lfog1 left_on_edge.
  rewrite pt_eqE /= !eqxx /=; congr (_ :: _ :: _); apply/eqP.
  by rewrite pt_eqE /= !eqxx.
case oca_eq: (opening_cells_aux _ _ _ _) => [s c].
rewrite pvertE //=.
have lfq : left_pt f = point e.
  by apply/eqP/oute'; rewrite mem_sort qsubo // inE eqxx.
have vf : valid_edge f (point e).
  by apply: valid_edge_extremities; rewrite lfq eqxx.
have qsub : {subset q <= outgoing e}.
  by move=> x xin; apply: qsubo; rewrite inE xin orbT.
by have := Ih le f lfq vf qsub; rewrite oca_eq /=.
Qed.

Lemma opening_cells_first_left_pts le he :
  valid_edge le (point e) ->
  outgoing e != nil ->
  point e >>> le ->
  left_pts 
     (head dummy_cell
     (opening_cells_aux (point e) (sort (@edge_below _) (outgoing e))
     le he).1)
 = point e :: Bpt (p_x (point e)) (pvert_y (point e) le) :: nil.
Proof.
move=> vle onn pal.
set W := sort _ _.
have sgt0 : (0 < size W)%N by rewrite /W size_sort; case : (outgoing e) onn.
case Wq : W sgt0 => [ // | g1 gs'] _ /=.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
rewrite pvertE //=.
case: ifP=> // samept.
have := pvert_on vle; rewrite -(eqP samept) => onle.
have /andP[/eqP pf _] := onle.
by move: pal; rewrite /point_under_edge pf le_eqVlt eqxx.
Qed.

Lemma update_open_cell_side_limit_ok new_op new_lsto:
  update_open_cell lsto e = (new_op, new_lsto) ->
  p_x (point e) = left_limit lsto ->
  point e <<< high lsto ->
  point e >>> low lsto ->
  all open_cell_side_limit_ok (rcons new_op new_lsto).
Proof.
rewrite /update_open_cell.
move=> + pxq puh pal /=.
have := (allP open_side_limit lsto lstoin).
rewrite /open_cell_side_limit_ok /= => /andP[] lptsno /andP[] alllpts.
move=> /andP[] slpts /andP[] athigh atlow.
case lptsq : (left_pts lsto) lptsno => [ // | p1 [ | p2 lpts']] _ /=.
  rewrite lptsq /= in athigh atlow.
  (* contradiction with puh pal *)
  have pxe1 : p_x (point e) = p_x p1 by rewrite pxq /left_limit lptsq.
  have := strict_under_edge_lower_y pxe1 athigh; rewrite puh=> /esym.
  have := under_edge_lower_y pxe1 atlow; rewrite (negbTE pal)=>/esym.
  move/negbT; rewrite -ltNge=> /lt_trans /[apply].
  by rewrite lt_irreflexive.
have pxe2 : p_x (point e) = p_x p2.
  rewrite (eqP (allP alllpts p2 _)); last by rewrite lptsq !inE eqxx orbT.
  exact pxq.
have p2lte : p_y p2 < p_y (point e).
  have := lex_left_limit; rewrite lptsq /= => /andP[] + _.
  by rewrite /lexPt pxe2 lt_irreflexive eqxx.
case ogq : (outgoing e) => [ | fog ogs].
  move=> [] <- <-; rewrite /= andbT /open_cell_side_limit_ok /=.
  have pxel : p_x (point e) = p_x (last p2 lpts').
    by rewrite pxq /left_limit lptsq.
  move: (alllpts); rewrite lptsq /= => /andP[] -> /andP[] /[dup] /eqP p2x -> ->.
  rewrite lptsq /= in athigh.
  have pxe1 : p_x (point e) = p_x p1.
    by have := alllpts; rewrite lptsq /= => /andP[] /eqP ->.
  have := strict_under_edge_lower_y pxe1 athigh; rewrite puh=> /esym ye1.
  move: (pxel) => /eqP ->; rewrite ye1.
  move: slpts; rewrite lptsq /= => /andP[] _ ->.
  by rewrite athigh; move: atlow; rewrite lptsq /= => ->; rewrite p2lte !andbT.
case oca_eq: (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
  have onn : outgoing e != [::] by rewrite ogq.
  have := opening_cells_aux_absurd_case vlo vho onn oute.
  by rewrite ogq oca_eq.
move=> -[] <- <- /=.
have ognn : outgoing e != [::] by rewrite ogq.
have := opening_cells_last_left_pts vlo vho ognn puh; rewrite /=.
rewrite ogq oca_eq /= => llnoq /=.
move: (alllpts); rewrite lptsq /= => /andP[] _ /andP[] -> ->.
move: pxq; rewrite /left_limit lptsq /= => ->; rewrite eqxx /=.
rewrite p2lte /=.
have := allP open_side_limit lsto lstoin => /andP[] _ /andP[] _.
rewrite lptsq /= => /andP[] /andP[] _ -> /andP[] _ llo.
have := opening_cells_seq_edge_shift _ vlo vho oca_eq.
rewrite -ogq => /(_ oute') /= -[] <- _; rewrite llo andbT.
have := opening_cells_aux_high vlo vho oute'; rewrite ogq oca_eq /= => highout.
apply/andP; split.
  have /oute'/eqP <- : high fno \in sort (@edge_below _) (outgoing e).
    by rewrite ogq -highout inE eqxx.
  by apply left_on_edge.
have := opening_cells_aux_side_limit vlo vho (underWC pal) puh oute'.
rewrite ogq oca_eq => /(_ _ _ erefl) allok.
by apply/allP=> x xin; apply: (allP allok x); rewrite /= inE xin orbT.
Qed.

Lemma size_left_lsto :
  p_x (point e) = lstx ->
  point e >>> low lsto ->
  point e <<= high lsto ->
  (1 < size (left_pts lsto))%N.
Proof.
move=> pxhere pal puh.
have lstok : open_cell_side_limit_ok lsto by apply: (allP open_side_limit).
case lptsq : (left_pts lsto) => [ | p1 [ | p2 lpts]] //.
  by move: lstok; rewrite /open_cell_side_limit_ok lptsq.
have /andP[p1onh p1onl] : (p1 === high lsto) && (p1 === low lsto).
  by move: lstok; rewrite /open_cell_side_limit_ok lptsq /= eqxx /=.
have /eqP samex : p_x (point e) = p_x p1.
  by have := pxhere; rewrite lstxq /left_limit lptsq /=.
suff : p_y (point e) < p_y (point e) by rewrite lt_irreflexive.
have := same_pvert_y vho samex. 
rewrite (on_pvert p1onh) => /eqP. 
have := under_pvert_y vho; move: (puh)=> /[swap] -> /[swap] ->.
move=> /le_lt_trans; apply.
have := under_pvert_y vlo; move: (pal) => /[swap] ->.  
have := same_pvert_y vlo samex => /eqP ->. 
by rewrite -ltNge (on_pvert p1onl).
Qed.

Lemma step_keeps_open_side_limit :
  all open_cell_side_limit_ok
    (state_open_seq (step e (Bscan fop lsto lop cls lstc lsthe lstx))).
Proof.
(* have := step_keeps_invariant1. *)
rewrite /step/=.
case: ifP=> [pxaway | /negbFE/eqP/[dup] pxhere/abovelstle palstol].
  case oe : (open_cells_decomposition (fop ++ lsto :: lop) (point e))=>
    [[[[[fc cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /state_open_seq /=.
(*  rewrite /invariant1 /inv1_seq /state_open_seq /==> - [_ [sval' [adj' _]]]. 
*)
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
  have [pal puh vle vhe _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe.
  rewrite -!catA !all_cat /=; apply/andP; split.
    apply/allP=> x xin; apply: (allP open_side_limit).
    by rewrite /open ocd; subset_tac.
  rewrite andbA; apply/andP; split; last first.
    apply/allP=> x xin; apply: (allP open_side_limit).
    by rewrite /open ocd; subset_tac.
  rewrite andbC -all_rcons.
  apply: (opening_cells_aux_side_limit _ vhe _ puh oute' oca_eq).
    by apply: open_edge_valid; rewrite /open.
  by apply: underWC.
case: ifP=> [eabove | ebelow].
  case oe: (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe' exi.
  have [pal puh vle vhe _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
  rewrite /state_open_seq /=.
  rewrite -(cat_rcons lsto) -catA all_cat;apply/andP; split.
    apply/allP=> x xin; apply: (allP open_side_limit).
    by rewrite ocd mem_cat xin.
  rewrite -cat_rcons all_cat; apply/andP; split; last first.
    apply/allP=> x xin; apply: (allP open_side_limit).
    by rewrite ocd; subset_tac.
  apply: (opening_cells_aux_side_limit _ vhe _ puh oute' oca_eq).
    by apply: open_edge_valid; rewrite /open.
  by apply: underWC.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  rewrite /state_open_seq /=.
  case uoc_eq : (update_open_cell lsto e) => [nos lno] /=.
  have pxhere' : p_x (point e) = left_limit lsto by rewrite pxhere.
  have puh : point e <<< high lsto by rewrite -lstheq.
  have nosok := update_open_cell_side_limit_ok uoc_eq pxhere' puh palstol.
  rewrite -catA -cat_rcons !all_cat nosok /= -all_cat.
  by apply: (all_sub _ open_side_limit); rewrite /open; subset_tac.
move/negbFE:ebelow => ebelow.
move/negbT: eonlsthe=> eonlsthe.
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have exi2 : exists2 c, c \in lsto :: lop & contains_point' (point e) c.
  by exists lsto; [subset_tac | rewrite /contains_point' palstol -lstheq].
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
have [fc'0 lelsto] := last_step_situation oe pxhere eonlsthe ebelow.
rewrite oe fc'0 lelsto cats0=> oe'.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe' exi.
have [pal puh vle vhe ncont] :=
    decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
rewrite /update_open_cell_top.
have lstok : open_cell_side_limit_ok lsto by apply: (allP open_side_limit).
have slpts : (1 < size (left_pts lsto))%N.
  by apply: size_left_lsto=> //; rewrite -lstheq.
case ogq : (outgoing e) => [ | fog ogs]; rewrite -?ogq; last first.
  have ognn : outgoing e != [::] by rewrite ogq.
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
    have := opening_cells_aux_absurd_case vlo vhe ognn oute.
    by rewrite oca_eq.
  rewrite /state_open_seq /=.
  have := opening_cells_aux_side_limit vlo vhe (underWC pal) puh oute' oca_eq.
  rewrite/=; move=> /andP[] fnook newok.
  rewrite -catA /= -(cat_rcons lno) all_cat /= all_cat newok /=.
  move: (open_side_limit); rewrite /open all_cat => /andP[] -> _.
  have -> : all open_cell_side_limit_ok lc.
    apply/allP=> x xin; apply: (allP open_side_limit x).
    by rewrite /open ocd !mem_cat inE xin ?orbT.
  rewrite /= ?andbT.
  rewrite /open_cell_side_limit_ok.
  rewrite /set_left_pts /=.
  have lfnoq : low fno = low lsto.
    have := opening_cells_seq_edge_shift oute' vlo vhe oca_eq.
  by rewrite /= => -[].
case lptsq : (left_pts lsto) slpts => [ | p1 [ | p2 lpts]] // _.
  move: (pxhere); rewrite /= lstxq /left_limit lptsq /= => /eqP -> /=.
  move: (lstok); rewrite /open_cell_side_limit_ok lptsq /=.
  move=> /andP[] /andP[] _ /[dup] xp2 -> /= /andP[] /andP[] _ ->.
  move=> /andP[] _ p2onl.
  move: xp2=> /andP[] xp2 _.
  rewrite lfnoq p2onl.
  have := lex_left_limit; rewrite lptsq /= => /andP[] + _.
  rewrite /lexPt lt_neqAle.
  have -> /= : (p_x p2 == p_x (point e)).
    by rewrite pxhere lstxq /left_limit lptsq /= xp2.
  move=> -> /=; rewrite andbT.
  have /oute/eqP <- : high fno \in outgoing e.
    have := opening_cells_aux_high vlo vhe oute'; rewrite oca_eq /=.
    set lg := (X in X = _ -> _) => sortq.
    have : high fno \in lg by rewrite /lg; subset_tac.
    by rewrite sortq mem_sort.
  by apply: left_on_edge.
(* Finished the case where there are some elements in outgoing e *)
rewrite /state_open_seq/= !cats0.
rewrite all_cat /=.
move: (open_side_limit); rewrite /open ocd !all_cat /=.
move=> /andP[] -> /andP[] _ /andP[] _ ->; rewrite /= ?andbT.
case lptsq : (left_pts lsto) slpts => [ | p1 [ | p2 lpts]] // _.
rewrite /open_cell_side_limit_ok /=.
have pxe : p_x (point e) = p_x (last p2 lpts).
  by rewrite pxhere lstxq /left_limit lptsq /=.
rewrite pxe eqxx /=.
move: (lstok); rewrite /open_cell_side_limit_ok lptsq /=.
move=> /andP[] /andP[] /[dup] /eqP p1x -> /andP[] -> ->.
move=> /andP[] /andP[] -> -> /andP[] p1on ->.
rewrite /= !andbT.
have p1e : p1 = (point e).
  have /eqP samex : p_x (point e) = p_x p1.
    by have := pxhere; rewrite lstxq /left_limit lptsq /= p1x.
  have /eqP samey : p_y (point e) = p_y p1.
    have eonlsthe' : point e === high lsto.
      by apply: under_above_on=> //; rewrite -lstheq // ?underW.
    by have /eqP := on_edge_same_point eonlsthe' p1on samex.
  by apply/esym/eqP; rewrite pt_eqE samex samey.
by rewrite p1e -strict_under_pvert_y // puh -pxe pvert_on.
Qed.

Lemma step_keeps_open_disjoint :
  {in state_open_seq (step e (Bscan fop lsto lop cls lstc lsthe lstx)) &,
     disjoint_open_cells R}.
Proof.
have := step_keeps_invariant1; rewrite /invariant1/inv1_seq. 
set s' := (state_open_seq _) => -[clae' [sval' [adj' [cbtom' srf']]]].
have := step_keeps_pw; rewrite -/s' => pw'.
have := step_keeps_open_side_limit; rewrite -/s'=> ok'.
apply: disoc=>//.
Qed.

(* This is not used, just now. *)
Lemma left_limit_closing_cells (cc : seq cell) (p1 : pt) :
  adjacent_cells cc -> seq_valid cc p1 ->
  p1 >>> low (head_cell cc) -> p1 <<< high (last_cell cc) ->
  all (contains_point p1) cc ->
  [seq left_limit i | i <- closing_cells p1 cc] = [seq left_limit i | i <- cc].
Proof.
move=> adjcc svalcc pale puhe allcont.
rewrite /closing_cells.
rewrite -map_comp; rewrite -eq_in_map /close_cell => -[] ls rs lo hi cin /=.
move: (allP svalcc _ cin) => /= /andP[] vloc vhic.
by rewrite (pvertE vloc) (pvertE vhic).
Qed.

Lemma right_limit_close_cell p1 c :
  valid_edge (low c) p1 -> valid_edge (high c) p1 ->
  right_limit (close_cell p1 c) = p_x p1.
Proof.
move=> vlc vhc; rewrite /close_cell /right_limit.
rewrite !pvertE //=.
by case: ifP; case: ifP.
Qed.

Lemma left_limit_close_cell p1 c :
   left_limit (close_cell p1 c) = left_limit c.
Proof.
rewrite /close_cell.
by do 2 (case: (vertical_intersection_point _ _) => //).
Qed.

Lemma step_keeps_disjoint_default :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) :=
      opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
    let closed := closing_cells (point e) cc in
     let last_closed := close_cell (point e) lcc in
     let closed_cells := cls ++ lstc :: rcons closed last_closed in
  {in closed_cells &, disjoint_closed_cells R} /\
  {in fc ++ nos ++ lno :: lc & closed_cells,
    disjoint_open_closed_cells R}.
Proof.
case oe : (open_cells_decomposition open (point e)) =>
   [[[[[fc  cc] lcc] lc] le] he].
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct
     [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe ncont]
 := connect_properties cbtom adj rfo sval bet_e ocd all_nct all_ct
  lcc_ctn flcnct.
have allcont : all (contains_point (point e)) (rcons cc lcc).
  by rewrite -cats1 all_cat /= lcc_ctn !andbT; apply/allP.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
move=> closed last_closed closed_cells.
have svalcc : seq_valid (rcons cc lcc) (point e).
   apply/allP=> c cin; apply: (allP sval); rewrite ocd !mem_cat.
   move: cin; rewrite mem_rcons inE.
   by move=> /orP[/eqP |] ->; rewrite ?inE ?eqxx ?orbT //.
have adjcc : adjacent_cells (rcons cc lcc).
  by move: adj; rewrite ocd -cat_rcons =>/adjacent_catW[] _ /adjacent_catW[].
have rfocc : s_right_form (rcons cc lcc).
   apply/allP=> c cin; apply: (allP rfo); rewrite ocd !mem_cat.
   move: cin; rewrite mem_rcons inE.
   by move=> /orP[/eqP |] ->; rewrite ?inE ?eqxx ?orbT //.
have closed_map : closing_cells (point e) (rcons cc lcc) =
       rcons [seq close_cell (point e) c | c <- cc]
          (close_cell (point e) lcc).
  by rewrite /closing_cells map_rcons.
have ccok : all open_cell_side_limit_ok (rcons cc lcc).
  apply/allP=> c cin; apply: (allP open_side_limit); rewrite ocd !mem_cat.
  move: cin; rewrite mem_rcons inE.
   by move=> /orP[/eqP |] ->; rewrite ?inE ?eqxx ?orbT //.
have := closing_cells_side_limit' rfocc svalcc adjcc ccok allcont.
rewrite head_rcons pal last_rcons puh=> /(_ isT isT).
rewrite [X in all _ X]closed_map=> /allP cl_sok.
have oldcl_newcl :
  {in rcons cls lstc & closing_cells (point e) (rcons cc lcc),
     disjoint_closed_cells R}.
  move=> c1 c2 c1in; rewrite closed_map -map_rcons=> /mapP[c2' c2'in c2eq].
  have c2'open : c2' \in open.
    by rewrite ocd -cat_rcons !mem_cat c2'in !orbT.
    have vc2 : valid_cell c2' (point e) by apply/andP/(allP sval).
  right; rewrite /c_disjoint=> q; apply/negP=> /andP[inc1 inc2].
  rewrite c2eq in inc2.
   case/negP:(disjoint_open_closed c2'open c1in q).
   rewrite inc1 andbT.
  apply:(close'_subset_contact vc2 _ inc2).
  by move: (cl_sok c2); rewrite c2eq; apply; rewrite -map_rcons; apply: map_f.
split.
  move=> c1 c2; rewrite !mem_cat !inE !orbA.
  move=> /orP[c1old | c1new] /orP[c2old | c2new].
         by apply: disjoint_closed; rewrite mem_rcons inE orbC.
      by apply: oldcl_newcl; rewrite ?mem_rcons ?inE 1?orbC // closed_map.
    apply: c_disjoint_eC; apply: oldcl_newcl.
      by rewrite mem_rcons inE orbC.
    by rewrite closed_map.
  rewrite -map_rcons in c1new c2new.
  move: c1new c2new => /mapP[c1' c1'in c1eq] /mapP[c2' c2'in c2eq].
  have c1'open : c1' \in open by rewrite ocd -cat_rcons !mem_cat c1'in orbT.
  have c2'open : c2' \in open by rewrite ocd -cat_rcons !mem_cat c2'in orbT.
  have vc1 : valid_cell c1' (point e) by apply/andP/(allP sval).
  have vc2 : valid_cell c2' (point e) by apply/andP/(allP sval).
  have [/eqP c1c2 | c1nc2] := boolP(c1' == c2').
    by left; rewrite c1eq c2eq c1c2.
  right=> q; apply/negP=> /andP[inc1 inc2].
  case: (disjoint_open c1'open c2'open)=> [/eqP | /(_ q)]. 
    by rewrite (negbTE c1nc2).
  move=> /negP[].
  rewrite c1eq in inc1; rewrite c2eq in inc2.
  rewrite (close'_subset_contact vc1 _ inc1); last first.
    by apply: cl_sok; rewrite -map_rcons; apply: map_f.
  rewrite (close'_subset_contact vc2 _ inc2) //.
  by apply: cl_sok; rewrite -map_rcons; apply: map_f.
rewrite -leq in vle; rewrite -heq in vhe.
move=> c1 c2; rewrite -cat_rcons 2!mem_cat orbCA=> /orP[c1newo |c1old] c2in.
  have rlc2 : right_limit c2 <= p_x (point e).
    move: c2in; rewrite /closed_cells -cat_rcons mem_cat.
    move=> /orP[/closed_right_limit // |].
    rewrite -map_rcons=> /mapP[c2' c2'in ->].
    by rewrite close_cell_right_limit //; apply/andP/(allP svalcc).
  move=> q; rewrite inside_open'E inside_closed'E; apply/negP.
  move=> /andP[] /andP[] _ /andP[] _ /andP[] + _
     /andP[] _ /andP[] _ /andP[] _ +.
  have := opening_cells_left oute vle vhe.
  rewrite /opening_cells oca_eq=> /(_ _ c1newo) => -> peq qrlc2.
  by move: rlc2; rewrite leNgt=>/negP[]; apply: (lt_le_trans peq).
have c1open : c1 \in open by rewrite ocd -cat_rcons !mem_cat orbCA c1old orbT.
move: c2in; rewrite /closed_cells -cat_rcons mem_cat=>/orP[c2old |].
  by apply: disjoint_open_closed.
rewrite -map_rcons=> /mapP[c2' c2'in c2eq] q; apply/negP=> /andP[] inc1 inc2.
have c2'open : c2' \in open by rewrite ocd -cat_rcons !mem_cat c2'in !orbT.
have [c1eqc2 | disjc1c2] := disjoint_open c1open c2'open.
  case: (decomposition_not_contain rfo sval adj cbtom bet_e oe c1old).
  rewrite c1eqc2.
  by move: c2'in; rewrite mem_rcons inE=> /orP[/eqP -> | /all_ct].
move: (disjc1c2 q); rewrite inc1 //=.
have vc2 : valid_cell c2' (point e) by apply/andP/(allP sval).
rewrite c2eq in inc2.
rewrite (close'_subset_contact vc2 _ inc2) //.
by apply: cl_sok; rewrite -map_rcons; apply: map_f.
Qed.

Definition set_right_pts (c : cell) (l : seq pt) :=
  Bcell (left_pts c) l (low c) (high c).

Lemma inside_closed_set_right_pts (c : cell) l q:
  last dummy_pt (right_pts c) = last dummy_pt l ->
  inside_closed' q c = inside_closed' q (set_right_pts c l).
Proof.
rewrite /inside_closed' /set_right_pts /inside_closed_cell /contains_point /=.
by rewrite /right_limit /= => ->.
Qed.

Lemma inside_closed'_update q1 q:
  inside_closed' q lstc = inside_closed' q (update_closed_cell lstc q1).
Proof.
have samer : last dummy_pt (right_pts lstc) =
             last dummy_pt (belast (head dummy_pt (right_pts lstc))
                             (behead (right_pts lstc)) ++
                           [:: q1; last dummy_pt (right_pts lstc)]).
  move: non_empty_right.
  elim/last_ind : (right_pts lstc) => [ // | rpts lr _] _ /=.
  by rewrite !last_cat /=.
rewrite /update_closed_cell.
have := inside_closed_set_right_pts q samer.
by rewrite /set_right_pts /= => <- //.
Qed.

Lemma update_open_cellE1 c c1 :
 valid_edge (low c) (point e) ->
 valid_edge (high c) (point e) ->
 open_cell_side_limit_ok c ->
 p_x (point e) = left_limit c ->
 (1 < size (left_pts c))%N ->
 point e >>> low c ->
 point e <<< high c ->
 c1 \in (update_open_cell c e).1 ->
 exists2 c', c' \in (opening_cells_aux (point e) 
                        (sort (@edge_below _) (outgoing e)) (low c)
    (high c)).1 &
     c1 = c' \/
     exists2 l, last dummy_pt l = last dummy_pt (left_pts c') &
     c1 = set_left_pts c' l.
Proof.
move=> vle vhe cok xcond sl pal puh.
rewrite /update_open_cell.
case ogq : (outgoing e) => [ | fog ogs] //=.
case oca_eq : (opening_cells_aux _ _ _ _) => [ [// | fno nos] lno] /=.
rewrite inE => /orP[/eqP -> | ].
  exists fno; first by rewrite inE eqxx.
  right; exists (point e :: behead (left_pts c)).
    case lptsq : (left_pts c) sl => [ // | p1 [ // | p2 lpts]] _ /=.
    move: cok; rewrite /open_cell_side_limit_ok=> /andP[] _ /andP[] allx.
    move=> /andP[] _ /andP[] _; rewrite lptsq /=.
    have oute2 : {in (fog :: ogs),
        forall g, left_pt g == point e}.
      by rewrite -ogq; exact oute.
    have oute3 : {in sort (@edge_below _) (fog :: ogs),
        forall g, left_pt g == point e}.
      by move=> g; rewrite mem_sort; apply: oute2.
    have := opening_cells_side_limit vle vhe (underWC pal) puh oute2.
    rewrite /opening_cells oca_eq=> /allP /(_ fno).
    rewrite inE eqxx=> /(_ isT)=> /andP[] _ /andP[] _ /andP[] _ /andP[] _.
    have := opening_cells_first_left_pts (high c) vle _ pal.
    rewrite ogq oca_eq => /(_ isT) /= -> /=.
    have [_ /= ] := adjacent_opening_aux' vle vhe oute3 oca_eq => ->.
    rewrite /=.
    move=> /on_edge_same_point /[apply] /=.
    rewrite xcond /left_limit lptsq /= eqxx => /(_ isT) /eqP ->.
    by apply/eqP; rewrite pt_eqE /= !eqxx.
  by [].
move=> c1in; exists c1; first by rewrite inE c1in orbT.
by left.
Qed.

Lemma update_open_cellE2 c :
 valid_edge (low c) (point e) ->
 valid_edge (high c) (point e) ->
 open_cell_side_limit_ok c ->
 p_x (point e) = left_limit c ->
 (1 < size (left_pts c))%N ->
 point e >>> low c ->
 point e <<< high c ->
 (update_open_cell c e).2 =
 (opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) (low c)
    (high c)).2 \/
  (update_open_cell c e).2 =
  (set_left_pts c (head dummy_pt
       (left_pts c) :: point e :: behead (left_pts c))).
Proof.
move=> vle vhe cok xcond sl pal puh.
rewrite /update_open_cell.
case ogq : (outgoing e)=> [ | fog ogs]; first by right.
left; rewrite -ogq.
case oca_eq : (opening_cells_aux _ _ _ _) => [ [ | fno nos] lno] //=.
have ognn : outgoing e != [::] by rewrite ogq.
have := opening_cells_aux_absurd_case vle vhe ognn oute.
by rewrite oca_eq.
Qed.

Lemma inside_open'_set_pts (c : cell) l1 l2 q :
   last dummy_pt l1 = last dummy_pt (left_pts c) ->
   inside_open' q c = inside_open' q (set_pts c l1 l2).
Proof.
move=> same_lim.
rewrite /inside_open' /inside_open_cell /contains_point /left_limit /=.
by rewrite same_lim.
Qed.

Lemma oc_disjoint_set_left_pts c1 c2 l :
  last dummy_pt l = last dummy_pt (left_pts c1) ->
  oc_disjoint c1 c2 ->
  oc_disjoint (set_left_pts c1 l) c2.
Proof.
move=> eql ref q.
rewrite -inside_open'_set_pts; last by apply/esym.
exact: (ref q).
Qed.

Lemma step_keeps_disjoint :
  let s' := step e (Bscan fop lsto lop cls lstc lsthe lstx) in
  {in state_closed_seq  s' &, disjoint_closed_cells R} /\
  {in state_open_seq s' & state_closed_seq s',
    disjoint_open_closed_cells R}.
Proof.
rewrite /step.
case: ifP=> [pxaway |/negbFE/eqP /[dup] pxhere /abovelstle palstol].
  case oe : (open_cells_decomposition open (point e)) =>
     [[[[[fc  cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /state_closed_seq /state_open_seq /=.
  have := step_keeps_disjoint_default; rewrite oe oca_eq /=.
  by rewrite rcons_cat /= =>-[]A B; split;[apply: A | rewrite -catA; apply: B].
case: ifP=> [eabove | ebelow].
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe' exi.
  have [pal puh vle vhe _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
  rewrite /state_open_seq /state_closed_seq /= rcons_cat.
  rewrite -(cat_rcons lsto) -catA -(cat_rcons lno).
  have := step_keeps_disjoint_default.
  by rewrite oe' oca_eq /= -(cat_rcons lno); apply.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  have oe : open_cells_decomposition open (point e) =
          (fop, [::], lsto, lop, low lsto, high lsto).
    by rewrite open_cells_decomposition_single=> //; rewrite -lstheq.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
  rewrite /state_open_seq /state_closed_seq /=.
  case uoc_eq : (update_open_cell lsto e) => [nos lno] /=.
  split.
    have lstcn : lstc \notin cls.
      by move: uniq_closed; rewrite rcons_uniq=> /andP[].
    have lstcin : lstc \in rcons cls lstc by rewrite mem_rcons inE eqxx.
    have in' c : c \in cls -> c \in rcons cls lstc.
      by move=> cin; rewrite mem_rcons inE cin orbT.
    have main c1 q: 
         c_disjoint c1 lstc -> 
         c_disjoint c1 (update_closed_cell lstc q).
      by move=> /[swap] q1 /(_ q1); rewrite -inside_closed'_update.
    move=> c1 c2; rewrite !mem_rcons !inE !(orbC _ (_ \in cls)).
    move=>/orP[c1in | /eqP ->] /orP[c2in | /eqP ->]; last by left.
        by apply: disjoint_closed; rewrite mem_rcons inE ?c1in ?c2in orbT.
      right; apply: main; case: (disjoint_closed (in' _ c1in) lstcin)=> //.
      by move: lstcn=> /[swap] <-; rewrite c1in.
    apply: c_disjoint_eC; right; apply: main.
    case: (disjoint_closed (in' _ c2in) lstcin)=> //.
    by move: lstcn=> /[swap] <-; rewrite c2in.
  have main c : 
     oc_disjoint c lstc ->
     oc_disjoint c (update_closed_cell lstc (point e)).
    by rewrite /oc_disjoint=> /[swap] q /(_ q); rewrite -inside_closed'_update.
  have := step_keeps_disjoint_default.
  have lstok : open_cell_side_limit_ok lsto.
    by apply: (allP open_side_limit); rewrite /open mem_cat /= inE eqxx orbT.
  have pxo : p_x (point e) = left_limit lsto by rewrite -lstxq.
  have slpts : (1 < size (left_pts lsto))%N.
    by apply: size_left_lsto=> //; rewrite -lstheq; apply: underW.
  have puh : point e <<< high lsto by rewrite -lstheq.
  have := update_open_cellE1 vlo vho lstok pxo slpts palstol puh.
  rewrite uoc_eq /=.
  have := update_open_cellE2 vlo vho lstok pxo slpts palstol puh.
  rewrite uoc_eq /=.
  rewrite oe.  
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos' lno'] /= helper2 helper1.
  move=> [] _ helper3.
  move=> c1 c2 c1in; rewrite mem_rcons inE => /orP[/eqP -> | ].
    apply: main.
    move: c1in; rewrite -!catA /= mem_cat=> /orP[c1f |].
      apply: disjoint_open_closed; last by rewrite mem_rcons inE eqxx.
      by rewrite /open mem_cat c1f.
    rewrite mem_cat=> /orP[].
      move=>/helper1 [c1' c1'in]=>- [-> | ].
        by apply: helper3; rewrite !mem_cat /= ?inE ?eqxx ?c1'in ?orbT.
      move=>[l lq ->] q.
      suff -> : inside_open' q (set_left_pts c1' l) = inside_open' q c1'.
        by apply: (helper3 c1' lstc _ _ q);
          rewrite !mem_cat ?c1'in ?inE ?eqxx ?orbT.
      by apply/esym/inside_open'_set_pts/esym.
    rewrite inE=> /orP[/eqP -> | ].
      case: helper2=> [ -> | -> ].
        by apply: helper3; rewrite !mem_cat /= ?inE ?eqxx ?orbT.
      set W := (set_left_pts _ _).    
      move=> q.
      suff -> : inside_open' q W = inside_open' q lsto.
        by apply: disjoint_open_closed;
         rewrite ?mem_rcons ?mem_cat /= ?inE ?eqxx ?orbT.
      apply/esym/inside_open'_set_pts.
      have := size_left_lsto pxhere palstol (underW puh).
      by case : (left_pts lsto) => [ | p1 [ | p2 lpts]].
    move=> c1f.
    by apply: disjoint_open_closed;
         rewrite ?mem_cat ?mem_rcons ?inE ?c1f ?eqxx ?orbT.
  move=> c2in.
  move: c1in; rewrite -catA !mem_cat /= => /orP[c1f |].
    by apply: disjoint_open_closed;
       rewrite ?mem_cat ?mem_rcons ?inE ?c1f ?eqxx ?c2in ?orbT.
  move=> /orP[/helper1 [c1' c1no'] |].
    move=> [-> | [l lq -> q] ].  
      by apply: helper3; rewrite ?mem_rcons ?mem_cat ?c1no' ?orbT ?c2in.
    suff -> : inside_open' q (set_left_pts c1' l) = inside_open' q c1'.
      by apply: helper3; rewrite !mem_cat ?c1'in ?inE ?c2in ?c1no' ?orbT.
    by apply/esym/inside_open'_set_pts/esym.
  rewrite inE=> /orP[/eqP -> | ].
    move: helper2=> [-> | ->].
      by apply: helper3; rewrite ?mem_cat ?inE ?eqxx ?c2in ?orbT.
    set W := (set_left_pts _ _).    
    move=> q.
    suff -> : inside_open' q W = inside_open' q lsto.
      by apply: disjoint_open_closed;
       rewrite ?mem_rcons ?mem_cat /= ?inE ?eqxx ?c2in ?orbT.
    apply/esym/inside_open'_set_pts.
    have := size_left_lsto pxhere palstol (underW puh).
    by case : (left_pts lsto) => [ | p1 [ | p2 lpts]].
  move=> c1f.
  by apply: disjoint_open_closed;
       rewrite ?mem_cat ?mem_rcons ?inE ?c1f ?c2in ?orbT.
rewrite /update_open_cell_top.
move : ebelow eonlsthe; rewrite lstheq=> /negbFE ebelow /negP/negP eonlsthe.
have ponlsthe : point e === lsthe.
  by rewrite lstheq; apply: under_above_on.
have exi2 : exists2 c, c \in (lsto :: lop) &
          contains_point' (point e) c.
  exists lsto; first by rewrite inE eqxx.
  by rewrite /contains_point' palstol ebelow.
case ogq : (outgoing e) => [ | fog og]; last first.
  case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
  rewrite oe=> oe'.
  have lelow : le = low lsto.
    move: oe; rewrite /open_cells_decomposition /=.
    have -> : contains_point (point e) lsto.
      by rewrite /contains_point ebelow underWC.
    case : (open_cells_decomposition_contact _ _) => [[[a b] c] |] /=;
      by move=> [] _ _ _ _ ->.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi2.
  have [pal puh vle vhe _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
    have ognn : outgoing e != nil by rewrite ogq.
    have:= opening_cells_aux_absurd_case vlo vhe ognn oute.
    by rewrite ogq oca_eq /=.
  rewrite /state_open_seq /state_closed_seq /=.
  have := step_keeps_disjoint_default; rewrite oe' ogq lelow oca_eq /=.
  move=> [] clsdisj ocdisj.
  split.           
    move=> x y xin yin; apply: clsdisj.
      move: xin; rewrite !(mem_rcons, inE, mem_cat).
      move=>/orP[-> | /orP[ | /orP[ ->| ->]]]; rewrite ?orbT //.
      by case: (cc) => /= [// | ? ?]; rewrite !inE /= => ->; rewrite ?orbT.
    move: yin; rewrite !(mem_rcons, inE, mem_cat).
    move=>/orP[-> | /orP[ | /orP[ ->| ->]]]; rewrite ?orbT //.
    by case: (cc) => /= [// | ? ?]; rewrite !inE /= => ->; rewrite ?orbT.
  move=> x y.
  rewrite !mem_cat !inE -!orbA !(orbCA _ (_ == set_left_pts _ _)).
  move=>/orP[]; last first.
    move=> xin yin; apply: ocdisj.
      rewrite !(mem_cat, inE).
      by move: xin=> /orP[-> | /orP[-> | ->]]; rewrite ?orbT //.
    move: yin; rewrite !(mem_rcons, mem_cat, inE).
    move=>/orP[-> | /orP[ | /orP[-> | ->] ]]; rewrite ?orbT //.
    by case: (cc) => /= [// | ? ?]; rewrite !inE /= => ->; rewrite ?orbT.
  move=> /eqP -> yin.
  apply: oc_disjoint_set_left_pts; last first.
    apply: ocdisj;[subset_tac | ].
    move: yin; rewrite !(mem_cat, inE, mem_rcons).
    move=> /orP[-> | /orP[ | /orP[-> | ->]]]; rewrite ?orbT //.
    by case: (cc) => /= [// | ? ?]; rewrite !inE /= => ->; rewrite ?orbT.
  have ognn : outgoing e != nil by rewrite ogq.
  have slsto := size_left_lsto pxhere palstol ebelow.
  have:= opening_cells_first_left_pts he vlo ognn palstol.
  rewrite ogq oca_eq /= => -> /=.
  move: slsto; case lptsq : (left_pts lsto) => [// | fp [// | sp lpts]] _ /=.
  have : open_cell_side_limit_ok lsto.
    by apply: (allP open_side_limit); rewrite /open mem_cat inE eqxx orbT.
  move=> /andP[] _ /andP[] A /andP[] _ /andP[] _ onlow.
  rewrite pxhere lstxq /left_limit lptsq /=.
  apply/eqP; rewrite pt_eqE /= eqxx /= eq_sym; apply/eqP.
  have -> : pvert_y (point e) (low lsto) = pvert_y (last sp lpts) (low lsto).
    apply/eqP; apply: same_pvert_y=> //.
    by rewrite pxhere lstxq /left_limit lptsq.
  by apply: on_pvert; move: onlow; rewrite lptsq.
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite oe /= => oe'.
rewrite /state_closed_seq /state_open_seq /=.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
  decomposition_main_properties oe' exi.
have [pal puh vle vhe _]:=
 decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
set nlsto := (X in (_ ++ X :: lc)).
have lelow : le = low lsto.
  move: oe; rewrite /open_cells_decomposition /=.
  have -> : contains_point (point e) lsto.
    by rewrite /contains_point ebelow underWC.
  case : (open_cells_decomposition_contact _ _) => [[[a b] c] |] /=;
    by move=> [] _ _ _ _ ->.
have := step_keeps_disjoint_default; rewrite oe' ogq lelow /=.
rewrite pvertE // pvertE //=.
have: {|p_x := p_x (point e); p_y := pvert_y (point e) he|} == point e = false.
  apply/negP=> abs.
  move: puh; rewrite strict_under_pvert_y // -[X in p_y X](eqP abs) /=.
  by rewrite lt_irreflexive.
have: point e == {|p_x := p_x (point e); p_y := pvert_y (point e) (low lsto)|}
   = false.
  apply/negP=> abs.
  move: pal; rewrite under_pvert_y // lelow [X in p_y X](eqP abs) /=.
  by rewrite le_eqVlt eqxx.
move=> -> -> [] clcnd clopcnd.
split.
  move=> x y xin yin; apply: clcnd.
    move: xin; rewrite !(mem_rcons, mem_cat, inE) orbCA=> /orP[]; last first.
      by move=> /orP[->| /orP[] ->]; rewrite ?orbT.
    by case: (cc) => //= a l; rewrite inE=> ->; rewrite ?orbT.
  move: yin; rewrite !(mem_rcons, mem_cat, inE) orbCA=> /orP[]; last first.
    by move=> /orP[->| /orP[] ->]; rewrite ?orbT.
  by case: (cc) => //= a l; rewrite inE=> ->; rewrite ?orbT.
rewrite cats0.
move=> x y xin yin.
have yin' : y \in cls ++ lstc :: rcons (closing_cells (point e) cc)
                            (close_cell (point e) lcc).
  move: yin; rewrite !(mem_rcons, mem_cat, inE) orbCA=> /orP[]; last first.
    by move=> /orP[-> | /orP[] ->]; rewrite ?orbT.
  by case: (cc) => //= ? ?; rewrite inE=> ->; rewrite ?orbT.
move: xin; rewrite !(mem_cat, mem_rcons, inE)=> /orP[xin | ].
  by apply: clopcnd; rewrite // !(mem_cat, mem_rcons, inE) xin.
move=>/orP[/eqP -> | xin]; last first.
  by apply: clopcnd; rewrite // !(mem_cat, mem_rcons, inE) xin ?orbT.
move=> q.
move: clopcnd; set w := (X in _ ++ X :: _).
have nlstoq : nlsto = set_pts w                      
   ({|p_x := p_x (point e); p_y := pvert_y (point e) he |} :: left_pts lsto)
   (right_pts lsto).
   by [].
move=> clopcnd.
rewrite nlstoq -inside_open'_set_pts.
  by apply: clopcnd; rewrite // !(mem_cat, mem_rcons, inE) eqxx ?orbT.
rewrite /w /=.
have /andP[] := allP open_side_limit lsto lstoin.
case plstq : (left_pts lsto) => [ // | a l] _ /= /andP[] A /andP[] _ /andP[] _.
move: lstxq; rewrite /left_limit plstq /= => sx one.
apply/eqP; rewrite pt_eqE /= pxhere sx eqxx /=.
rewrite -(on_pvert one); apply: same_pvert_y; first by case/andP: one.
by rewrite pxhere sx.
Qed.

Lemma step_keeps_injective_high_default :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) :=
      opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
    {in fc ++ nos ++ lno :: lc &, injective (@high R)}.
Proof.
  case oe : open_cells_decomposition => [[[[[fc cc] lcc] lc] le] he].
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct
     [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe ncont]
 := connect_properties cbtom adj rfo sval bet_e ocd all_nct all_ct
  lcc_ctn flcnct.
have dupcase c1 c2 : (c1 \in fc) || (c1 \in lc) ->
   c2 \in opening_cells (point e) (outgoing e) le he ->
   high c1 = high c2 -> c1 = c2.
  move=> c1in; rewrite leq heq => c2in hc1c2.
  have v1 : valid_edge (high c1) (point e).
    move: sval=> /allP /(_ c1); rewrite ocd -cat_rcons !mem_cat orbCA c1in orbT.
    by move=> /(_ isT) /andP[].
  have v2 : valid_edge (high c2) (point e).
    have /andP[ _ ] := opening_cells_subset vle vhe oute c2in.
    rewrite inE=> /orP[/eqP -> // | ].
    by have := opening_valid oute vle vhe => /allP /(_ _ c2in) /andP[].
  have : point e <<< high c1 \/ point e >>> high c1.
    move: c1in=> /orP[] c1in.
      right.
      by have := decomposition_above_high_fc oe cbtom adj bet_e rfo sval c1in.
    left.
    have [s1 [s2 lcq]] := mem_seq_split c1in.
    case s2q : s2 => [ | c1' s2'].
      move: inbox_e=> /andP[] /andP[] _ + _.
      suff -> : high c1 = top by [].
      move: cbtom=> /andP[] _ /eqP; rewrite ocd lcq s2q /=.
      by rewrite !(last_cat, last_cons) /=.
    have c1'in : c1' \in lc by rewrite lcq s2q mem_cat !inE eqxx !orbT.
    have := decomposition_under_low_lc oe cbtom adj bet_e rfo sval c1'in.
    suff -> : high c1 = low c1' by [].
    move: adj; rewrite /adjacent_cells ocd=> /sorted_catW /andP[] _.
    move=> /sorted_catW /andP[] _; rewrite lcq s2q.
    by rewrite /= -cat_rcons cat_path last_rcons /= => /andP[] _ /andP[] /eqP.
  have /andP[lows ] := opening_cells_subset vle vhe oute c2in.
  rewrite inE => /orP[/eqP hc1he | ]; last first.
    rewrite hc1c2 => /oute/eqP <-.
    move=> [ | ].
      rewrite strict_nonAunder; last first.
        by apply valid_edge_extremities; rewrite eqxx ?orbT.
      by rewrite left_on_edge.
    rewrite under_onVstrict ?left_on_edge //.
    by apply valid_edge_extremities; rewrite eqxx ?orbT.
  have c1hec : c1 = lcc.
    apply: high_inj.
        by rewrite ocd -cat_rcons!mem_cat orbCA c1in orbT.
      by rewrite ocd !(mem_cat, inE) eqxx !orbT.
    by rewrite hc1c2.
  have := decomposition_not_contain rfo sval adj cbtom bet_e oe c1in.
  by rewrite c1hec lcc_ctn.
have henout : he \notin outgoing e.
  apply/negP=> /oute /eqP abs.
  have := bottom_left_lex_to_high cbtom adj rfo open_side_limit inbox_e btm_left.
  move=> /(_ lcc); rewrite ocd !(mem_cat, inE) eqxx !orbT => /(_ isT).
  by rewrite -heq abs lexPt_irrefl.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
move=> c1 c2; rewrite -cat_rcons !mem_cat orbCA=> /orP[] c1in; last first.
  rewrite orbCA=> /orP[] c2in; last first.
    by apply: high_inj; rewrite ocd -cat_rcons !mem_cat orbCA ?c1in ?c2in ?orbT.
  by apply: (dupcase _ c2 c1in); rewrite /opening_cells oca_eq.
rewrite orbCA=> /orP[] c2in; last first.
  move/esym=> tmp; apply/esym; move: tmp.
  by apply: (dupcase _ c1 c2in); rewrite /opening_cells oca_eq.
have : uniq (rcons (sort (@edge_below _) (outgoing e)) he).
  by rewrite rcons_uniq mem_sort henout sort_uniq.
rewrite heq -(opening_cells_high vle vhe oute) => /uniq_map_injective; apply.
all: rewrite /opening_cells -heq -leq oca_eq; by [].
Qed.

(* TODO : propose for inclusion in math-comp *)
Lemma uniq_index (T : eqType) (x : T) l1 l2 :
   uniq (l1 ++ x :: l2) -> index x (l1 ++ x :: l2) = size l1.
Proof.
elim: l1 => [/= | a l1 Ih]; first by rewrite eqxx.
rewrite /= => /andP[].
case: ifP => [/eqP -> | _ _ /Ih -> //].
by rewrite mem_cat inE eqxx orbT.
Qed.
  
Lemma index_map_in (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) :
  {in s &, injective f} -> {in s, forall x, index (f x) [seq f i | i <- s] = index x s}.
Proof.
elim: s => [ // | a s Ih] inj x xin /=.
case: ifP => [/eqP/inj| fanfx].
  rewrite inE eqxx; move=> /(_ isT xin) => ->.
  by rewrite eqxx.
case: ifP=> [/eqP ax | xna ]; first by rewrite ax eqxx in fanfx.
congr (_.+1).
apply: Ih=> //.
  by move=> x1 x2 x1in x2in; apply: inj; rewrite !inE ?x1in ?x2in ?orbT.
by move: xin; rewrite inE eq_sym xna.
Qed.

Lemma update_cells_injective_high l1 l2 l2' l3:
  uniq (l1 ++ l2 ++ l3) ->
  [seq high c | c <- l2] = [seq high c | c <- l2'] ->
  {in l1 ++ l2 ++ l3 &, injective (@high R)} ->
  {in l1 ++ l2' ++ l3 &, injective (@high R)}.
Proof.
move=> u2 eqh inj0 x1 x2; rewrite !mem_cat orbCA=> x1in.
rewrite orbCA=> x2in hx1x2.
move: x1in=> /orP[x1l2' | x1in]; last first.
  move: x2in=> /orP[x2l2' | x2in]; last first.
    by move: hx1x2; apply: inj0; rewrite !mem_cat orbCA ?x1in ?x2in ?orbT.
  move: u2; rewrite uniq_catCA cat_uniq=> /andP[] _ /andP[] /negP abs _.
  have : high x2 \in [seq high c | c <- l2].
    by rewrite eqh; apply: map_f.
  move=> /mapP[x20 x20in hx20].
  rewrite -hx1x2 in hx20.
  have x1x20: x1 = x20.
    by apply: inj0; rewrite // ?mem_cat orbCA ?x20in ?x1in ?orbT.
  case: abs; apply/hasP; exists x20=> //.
  by rewrite -x1x20 mem_cat.
move: x2in=> /orP[x2l2'| x2in]; last first.
  move: u2; rewrite uniq_catCA cat_uniq=> /andP[] _ /andP[] /negP abs _.
  have : high x1 \in [seq high c | c <- l2].
    by rewrite eqh; apply: map_f.
  move=> /mapP[x10 x10in hx10].
  rewrite hx1x2 in hx10.
  have x2x10: x2 = x10.
    by apply: inj0; rewrite // !mem_cat orbCA ?x10in ?x2in ?orbT.
  case: abs; apply/hasP; exists x10=> //.
  by rewrite -x2x10 mem_cat.
remember (index x1 l2') as j1 eqn:j1def.
remember (index x2 l2') as j2 eqn:j2def.
have inj2 : {in l2 &, injective (high (R := R))}.
  by move=> u1 {}u2 uin1 uin2; apply: inj0; rewrite !mem_cat ?uin1 ?uin2 orbT.
have ul2 : uniq l2.
  by move: u2; rewrite !cat_uniq=> /andP[] _ /andP[] _ /andP[].
have uh : uniq [seq high c | c <- l2].
  by rewrite (map_inj_in_uniq inj2).
have := nth_index dummy_cell x1l2'; rewrite -j1def => j1q.
have := nth_index dummy_cell x2l2'; rewrite -j2def => j2q.
have j1lt : (j1 < size l2')%N by rewrite j1def index_mem.
have j2lt : (j2 < size l2')%N by rewrite j2def index_mem.
have : nth (high dummy_cell) [seq high c | c <- l2'] j1 = high x1.
  by rewrite (nth_map dummy_cell) // j1q.
have : nth (high dummy_cell) [seq high c | c <- l2'] j2 = high x1.
  by rewrite hx1x2 (nth_map dummy_cell) // j2q.
move=> <-; rewrite -eqh. 
move: uh=> /uniqP => /(_ dummy_edge); rewrite [X in size X]eqh size_map.
move=> /(_ j1 j2); rewrite !inE => /(_ j1lt j2lt) /[apply].
by rewrite -j1q -j2q => ->.
Qed.

Lemma opening_cells_aux_uniq q l g1 g2 r1 r2:
  uniq l ->
  g2 \notin l ->
  {in l, forall g, left_pt g == q} ->
  valid_edge g1 q ->
  valid_edge g2 q ->
  opening_cells_aux q l g1 g2 = (r1, r2) ->
  uniq (rcons r1 r2).
Proof.
move=> ul g2nin ol v1 v2 oca_eq.
have lg2 := opening_cells_aux_high_last v1 v2 ol.
have lg1 := opening_cells_aux_high v1 v2 ol.
apply: (@map_uniq _ _ (@high _)).
rewrite map_rcons rcons_uniq.
rewrite oca_eq /= in lg2 lg1.
by rewrite lg2 lg1 g2nin ul.
Qed.

Lemma opening_cells_contains_point le he nos:
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  point e >>> le ->
  point e <<< he ->
  opening_cells (point e) (outgoing e) le he = nos ->
  {in nos, forall c, contains_point (point e) c}.
Proof.
move=> vle vhe pal puh oceq.
have := opening_cells_aux_subset vle vhe oute'.
move: oceq; rewrite /opening_cells.
case oca_eq : (opening_cells_aux _ _ _ _)=> [nos' lno'] <- /(_ _ _ _ erefl).
move=> main x xin; rewrite /contains_point.
move: (main x xin); rewrite !inE=> /andP[] lows highs.
apply/andP; split.
  move: lows=> /orP[/eqP -> | /oute'/eqP <-]; first by rewrite underWC.
  by rewrite left_pt_above.
move: highs=> /orP[/eqP -> | /oute'/eqP <-]; first by rewrite underW.
by rewrite left_pt_below.
Qed.

Lemma step_keeps_uniq_default fc cc lcc lc le he nos lno:
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he = (nos, lno) ->
  uniq (fc ++ nos ++ lno :: lc).
Proof.
move=> oe oca_eq.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe old_nctn]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe.
have := opening_cells_contains_point vle vhe pal puh.
rewrite /opening_cells oca_eq => /(_ _ erefl)=> new_ctn.
have uo : uniq (sort (@edge_below _) (outgoing e)) by rewrite sort_uniq.
have heno : he \notin (sort (@edge_below _) (outgoing e)).
  apply/negP=> /oute'/eqP; move: puh=> /[swap] <-.
  by rewrite (negbTE (left_pt_above he)).
have uniqnew := opening_cells_aux_uniq uo heno oute' vle vhe oca_eq.
rewrite -cat_rcons uniq_catCA cat_uniq uniqnew.
move: uniq_open; rewrite ocd -cat_rcons uniq_catCA cat_uniq=> /andP[] _.
move=>/andP[] _ ->; rewrite andbT /= -all_predC /=.
apply/allP=> x /=; rewrite mem_cat=> /old_nctn nctn.
by apply/negP=> /new_ctn/nctn.
Qed.

Lemma step_keeps_injective_high :
  let s' := step e (Bscan fop lsto lop cls lstc lsthe lstx) in
  {in state_open_seq s' &, injective (@high R)}.
Proof.
rewrite /step.
case: ifP=> [pxaway |/negbFE/eqP /[dup] pxhere /abovelstle palstol].
  case oe : (open_cells_decomposition open (point e)) =>
     [[[[[fc  cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /state_closed_seq /state_open_seq /=.
  have := step_keeps_injective_high_default; rewrite oe oca_eq /=.
  by rewrite catA.
case: ifP=> [eabove | ebelow].
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe' exi.
  have [pal puh vle vhe _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
  rewrite /state_open_seq.
  rewrite -(cat_rcons lsto) -catA -(cat_rcons lno).
  have := step_keeps_injective_high_default.
  by rewrite oe' oca_eq /= !catA -cat_rcons.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  have oe : open_cells_decomposition open (point e) =
          (fop, [::], lsto, lop, low lsto, high lsto).
    by rewrite open_cells_decomposition_single=> //; rewrite -lstheq.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
  rewrite /state_open_seq /=.
  case uoc_eq : (update_open_cell _ _) => [nos lno] /=.
  rewrite -catA -cat_rcons.
  move: uoc_eq; rewrite /update_open_cell.
  case ogq : (outgoing e) => [ | fog ogs].
    move=> [] <- <-; rewrite [rcons _ _]/=.
    have uniqlsto : uniq (fop ++ [:: lsto] ++ lop).
      by move: uniq_open; rewrite /open.
    set w := (X in fop ++ X ++ lop).
    have samehigh : [seq high c | c <- [:: lsto]] = [seq high c | c <- w] by rewrite /=.
    by apply: (update_cells_injective_high uniqlsto samehigh).
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos'] lno'].
    have ogn : outgoing e != [::] by rewrite ogq.
    have := opening_cells_aux_absurd_case vlo vho ogn oute.
    by rewrite ogq oca_eq.
  move=> [] <- <-.
  have := step_keeps_injective_high_default.
  rewrite oe ogq oca_eq -cat_rcons.
  apply: update_cells_injective_high.
    have := step_keeps_uniq_default oe; rewrite ogq=> /(_ _ _ oca_eq).
    by rewrite cat_rcons catA.
  by rewrite !map_rcons.
case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc'] lcc'] lc'] le'] he'].
have lsto_ctn : contains_point' (point e) lsto.
  rewrite /contains_point' palstol -lstheq.
  by move: ebelow=> /negbT; rewrite negbK.
have exi2 : exists2 c, c \in lsto :: lop & contains_point' (point e) c.
  by exists lsto; [rewrite inE eqxx | ].
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe' exi2.
rewrite /update_open_cell_top.
case ogq : (outgoing e) => [ | fog ogs] /=.
  rewrite /state_open_seq /= cats0 -cat1s.
  have : {in fop ++ fc' ++ [:: lcc'] ++ lc' &, injective (@high R)}.
    have subtmp : {subset fop ++ fc' ++ lcc' :: lc' <= open}.
      move=> x; rewrite /open ocd !(mem_cat, inE).
      repeat (move=> /orP[ -> | ]; rewrite ?orbT //).
      by move=> ->; rewrite ?orbT.
    by move=> x y xin yin; apply: high_inj; apply: subtmp.
  rewrite catA.
  apply: update_cells_injective_high.
    rewrite cat_uniq; move: uniq_open; rewrite /open ocd catA.
    rewrite [X in is_true X -> _]cat_uniq=> /andP[] -> /= /andP[].
    rewrite has_cat negb_or => /andP[] _ /= => ->.
    by rewrite [X in is_true X -> _]cat_uniq => /andP[] _ /andP[] _.
  by rewrite /= heq.
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite oe' => oe.
have [pal puh vle vhe _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe.
case oca_eq : (opening_cells_aux _ _ _ _) => [ [ | fno nos] lno].
  have ogn : fog :: ogs != nil by [].
  have := opening_cells_aux_absurd_case vlo vhe ogn.
  by rewrite -[X in {in X, _}]ogq oca_eq => /(_ oute).
rewrite /state_open_seq /= !catA -(catA (_ ++ _)) -cat_rcons.
have := step_keeps_injective_high_default.
rewrite oe ogq.
have le'q : le' = low lsto.
  have := last_step_situation oe' pxhere.
  rewrite eonlsthe=> /(_ isT).
  by move: ebelow=> /negbT; rewrite negbK=> -> /(_ isT)[].
rewrite le'q oca_eq -cat_rcons.
apply: update_cells_injective_high=> //.
have := step_keeps_uniq_default oe; rewrite ogq le'q=> /(_ _ _ oca_eq).
by rewrite cat_rcons !catA.
Qed.

Lemma closing_cells_to_the_left fc cc lcc lc le he :
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  {in closing_cells (point e) cc, forall c, right_limit c <= p_x (point e)} /\
  right_limit (close_cell (point e) lcc) <= p_x (point e).
Proof.
move=> oe.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe _]:=
  decomposition_connect_properties rfo sval adj cbtom bet_e oe.
split; last first.
  have vlolcc : valid_edge (low lcc) (point e).
    apply: (proj1 (andP (allP sval lcc _))).
    by rewrite ocd !(mem_cat, inE) eqxx ?orbT.
  rewrite /close_cell (pvertE vlolcc).
  rewrite -heq (pvertE vhe) /right_limit /=.
  by case: ifP; case: ifP.
move=> c /mapP[c' c'in ->].
have c'in2 : c' \in open by rewrite ocd !mem_cat c'in ?orbT.
have /andP[vlc vhc] := allP sval c' c'in2.
rewrite /close_cell (pvertE vlc) (pvertE vhc) /=.
by case: ifP; case: ifP.
Qed.

Lemma step_keeps_closed_to_the_left :
  let s' := step e (Bscan fop lsto lop cls lstc lsthe lstx) in
  {in state_closed_seq s', forall c, right_limit c <= p_x (point e)}.
Proof.
rewrite /step.
case: ifP => [pxaway | /negbFE/eqP/[dup] pxhere /abovelstle palstol].
  case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /state_closed_seq /=.
  have [ccP lccP] := closing_cells_to_the_left oe.
  move=> x; rewrite mem_rcons inE => /orP[/eqP -> // | ].
  by rewrite -cat_rcons mem_cat => /orP[/closed_to_left | /ccP].
case: ifP=> [eabove | ebelow].
  case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  move: adj rfo sval; rewrite /open -cat_rcons => adj' rfo' sval'.
  have := open_cells_decomposition_cat adj' rfo' sval' (exi' eabove) eabove'.
  rewrite oe' cat_rcons => oe.
  have [ccP lccP] := closing_cells_to_the_left oe.
  rewrite /state_closed_seq /=.
  move=> x; rewrite mem_rcons inE => /orP[/eqP -> // | ].
  by rewrite -cat_rcons mem_cat => /orP[ /closed_to_left | /ccP].
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  case uoc_eq : (update_open_cell _ _) => [nos lno].
  rewrite /state_closed_seq /=.
  move=> x; rewrite mem_rcons inE => /orP[/eqP -> | ].
    rewrite /update_closed_cell /right_limit /=.
    have := non_empty_right; case pts_eq: (right_pts lstc) => [| p1 rpts] // _.
    rewrite /= last_cat /=.
    have /closed_to_left: lstc \in rcons cls lstc by rewrite mem_rcons inE eqxx.
    by rewrite /right_limit pts_eq.
  move=> xin.
  have /closed_to_left : x \in rcons cls lstc by rewrite mem_rcons inE xin orbT.
  by [].
case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
case uoct_eq : (update_open_cell_top _ _ _) => [nos lno].
have exi2 : exists2 c, c \in (lsto :: lop) &
          contains_point' (point e) c.
  exists lsto; first by rewrite inE eqxx.
  by rewrite /contains_point' palstol -lstheq (negbFE ebelow).
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite oe' => oe.
rewrite /state_closed_seq /=.
have [ccP lccP] := closing_cells_to_the_left oe.
move=> x; rewrite mem_rcons inE => /orP[/eqP -> // |].
rewrite mem_cat=> /orP[xin | ].
  have /ccP // : x \in closing_cells (point e) cc.
  by move/mapP: xin=> [] x' x'in ->; apply/map_f/mem_behead.
by rewrite -mem_rcons; apply: closed_to_left.
Qed.

Lemma outgoing_high_opening g le he:
   valid_edge le (point e) -> valid_edge he (point e) ->
   g \in (outgoing e) ->
   exists2 c, c \in opening_cells (point e) (outgoing e) le he & high c = g.
Proof.
move=> vle vhe gin.
have : g \in rcons (sort (@edge_below _) (outgoing e)) he.
  by rewrite mem_rcons inE mem_sort gin orbT.
by rewrite -(opening_cells_high vle vhe oute)=> /mapP[c cin ->]; exists c.
Qed.

Lemma step_keeps_left_pt_open_lex_default fc cc lcc lc le he nos lno:
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he =
     (nos, lno) ->
  {in fc ++ nos ++ lno :: lc & future_events,
     forall c e', lexPt (left_pt (high c)) (point e')}.
Proof.
move=> oe oca_eq.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe old_nctn]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe.
move=> c e' + e'in.
have e'in2 : e' \in e :: future_events by rewrite inE e'in orbT.
rewrite -cat_rcons !mem_cat orbCA=> /orP[]; last first.
  move=> cin; apply: left_pt_open_lex; last by [].
  by rewrite ocd -cat_rcons !mem_cat orbCA cin orbT.
move=> cino.
have := opening_cells_subset vle vhe oute; rewrite /opening_cells oca_eq.
move=> /(_ _ cino) /andP[] _.
rewrite inE => /orP[/eqP -> | ].
  rewrite heq; apply: left_pt_open_lex; last by [].
  by rewrite ocd !mem_cat !inE eqxx ?orbT.
move=> /oute/eqP ->.
by move: (order_path_min (@lexPtEv_trans _) sort_evs)=>/allP; apply.
Qed.

Lemma step_keeps_left_pt_open_lex :
  let s' :=  step e (Bscan fop lsto lop cls lstc lsthe lstx) in
  {in state_open_seq s' & future_events,
    forall c e', lexPt (left_pt (high c)) (point e')}.
Proof.
rewrite /step.
case: ifP => [pxaway | /negbFE/eqP/[dup] pxhere /abovelstle palstol].
  case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /state_open_seq /= -catA.
  apply: (step_keeps_left_pt_open_lex_default oe oca_eq).
case: ifP=> [eabove | ebelow].
  case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  move: adj rfo sval; rewrite /open -cat_rcons => adj' rfo' sval'.
  have := open_cells_decomposition_cat adj' rfo' sval' (exi' eabove) eabove'.
  rewrite oe' cat_rcons => oe.
  rewrite /state_open_seq /= -catA.
  have := (step_keeps_left_pt_open_lex_default oe oca_eq).
  by rewrite cat_rcons -!catA.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  rewrite /update_open_cell.
  case ogq : (outgoing e) => [ /= | fog ogs].
    rewrite /state_open_seq /= cats0 => x e' + e'in.
    have e'in2 : e' \in e :: future_events by rewrite inE e'in orbT.
    rewrite mem_cat inE orbCA /set_left_pts /= => /orP[/eqP -> /=| xin ].
      by apply: left_pt_open_lex; rewrite // /open mem_cat inE eqxx orbT.
    by apply: left_pt_open_lex; rewrite // /open mem_cat inE orbCA xin orbT.
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
    have ogn : outgoing e != [::] by rewrite ogq.
    have := opening_cells_aux_absurd_case vlo vho ogn oute.
    by rewrite ogq oca_eq.
  rewrite /state_open_seq /=.
  have sub1 : {subset (lno :: fno :: nos) ++ (fop ++ lop) <=
                  fop ++ (fno :: nos) ++ lno :: lop}.
    move=> x; rewrite !(mem_cat, inE) -!orbA.
    repeat move=> /orP[-> | ]; rewrite ?orbT//.
    by move=> ->; rewrite ?orbT.
  rewrite -catA -cat_rcons=> x e' + e'in.
  have := open_cells_decomposition_single adj rfo sval palstol.
  rewrite -lstheq ebelow_st => /(_ isT) oe.
  have := step_keeps_left_pt_open_lex_default oe.
  rewrite ogq lstheq oca_eq => /(_ _ _ erefl _ e' _ e'in) main.
  rewrite 2!mem_cat orbCA=> /orP[| xin]; last first.
    by apply/main/sub1; rewrite !mem_cat xin ?orbT.
  rewrite mem_rcons inE => /orP[/eqP xq | ].
    by apply/main/sub1; rewrite xq !(mem_cat, inE) eqxx.
  rewrite inE => /orP[/eqP xq | xin ].
    have /main : fno \in fop ++ (fno :: nos) ++ lno :: lop.
      by rewrite !(mem_cat, inE, eqxx, orbT).
    by have -> : high x = high fno by rewrite xq.
  by apply/main/sub1; rewrite !(mem_cat, inE, xin, orbT).
case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have exi2 : exists2 c, c \in (lsto :: lop) & contains_point' (point e) c.
  have : contains_point' (point e) lsto.
    by rewrite /contains_point' palstol -lstheq (negbFE ebelow).
  by exists lsto;[rewrite inE eqxx | ].
have := open_cells_decomposition_cat adj rfo sval exi2.
rewrite /= oe' => /(_ palstol)=> oe.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
rewrite /update_open_cell_top.
case ogq : (outgoing e) => [ | fog ogs].
  rewrite /state_open_seq /= => x e' + e'in.
  have e'in2 : e' \in e :: future_events by rewrite inE e'in orbT.
  rewrite mem_cat=> /orP[].
    rewrite cats0=> xin; apply: left_pt_open_lex => //.
    by rewrite /open ocd mem_cat xin.
  rewrite inE heq=> /orP[/eqP -> /= | ].
    have lccin : lcc \in open by rewrite /open ocd !(mem_cat, inE, eqxx, orbT).
    by apply: left_pt_open_lex.
  move=> A; have B: x \in open by rewrite /open ocd !(mem_cat, inE, A, orbT).
  by apply: left_pt_open_lex.
case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
rewrite /state_open_seq /=.
  have [pal puh vle vhe old_nctn]:=
     decomposition_connect_properties rfo sval adj cbtom bet_e oe.
  have ogn : fog :: ogs != [::] by [].
  have := opening_cells_aux_absurd_case vlo vhe ogn.
  by rewrite -[X in {in X, _}]ogq oca_eq=> /(_ oute).
rewrite /state_open_seq /= => x e' + e'in.
have e'in2 : e' \in e :: future_events by rewrite inE e'in orbT.
rewrite catA 3!mem_cat -orbA=> /orP[xin |].
  apply: left_pt_open_lex => //.
  by rewrite /open ocd 2!mem_cat xin.
have leq2 : le = low lsto.
  have := last_step_situation oe' pxhere.
  rewrite eonlsthe=> /(_ isT).
  by move: ebelow=> /negbT; rewrite negbK=> -> /(_ isT)[].
have main := step_keeps_left_pt_open_lex_default oe.
rewrite inE -orbA => /orP[/eqP -> | xin].
  have fnoin : fno \in (fop ++ fc') ++ (fno :: nos) ++ lno :: lc.
    by rewrite !(mem_cat, inE, eqxx, orbT).
  by move: main; rewrite ogq leq2 oca_eq=> /(_ _ _ erefl _ _ fnoin e'in).
move: main; rewrite ogq leq2 oca_eq=> /(_ _ _ erefl x e' _ e'in).
by apply; rewrite !mem_cat inE -!orbA xin ?orbT.
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

