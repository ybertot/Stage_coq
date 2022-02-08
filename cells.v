From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import math_comp_complements.
Require Import points_and_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section transitivity_proof.

Variables (T : eqType) (r : rel T) (s1 s2 : mem_pred T).

Hypothesis s1tr : {in s1 & &, transitive r}.
Hypothesis s2tr : {in s2 & &, transitive r}.
Hypothesis s1s2 : {in s1 & s2, forall x y, r x y && ~~ r y x}.

Lemma two_part_trans : {in predU s1 s2 & &, transitive r}.
Proof.
move=> x2 x1 x3 /orP[x2ins1 | x2ins2] /orP[x1ins1 | x1ins2]
      /orP[x3ins1 | x3ins2];
  try solve[move=> ?; apply:s1tr=> // |
            move=> ?; apply: s2tr => // |
            move=> ? ?; apply: (proj1 (andP (s1s2 _ _))) => //].
- by move=> r12 r23; move: (s1s2 x2ins1 x1ins2); rewrite r12 andbF.
- by move=> r12 r23; move: (s1s2 x2ins1 x1ins2); rewrite r12 andbF.
- by move=> r12 r23; move: (s1s2 x3ins1 x2ins2); rewrite r23 andbF.
- by move=> r12 r23; move: (s1s2 x3ins1 x2ins2); rewrite r23 andbF.
Qed.

End transitivity_proof.

Section working_environment.

Variable R : realFieldType.

Notation pt := (pt R).
Notation edge := (edge R).

Record cell := Bcell  {left_pts : list pt; right_pts : list pt;
                        low : edge; high : edge}.

Definition cell_eqb (ca cb : cell) : bool :=
  let: Bcell lptsa rptsa lowa higha := ca in
  let: Bcell lptsb rptsb lowb highb:= cb in
  (lptsa == lptsb) && (rptsa == rptsb) && (lowa == lowb) && (higha == highb).

Lemma cell_eqP : Equality.axiom cell_eqb.
Proof.
rewrite /Equality.axiom.
move => [lptsa rptsa lowa higha] [lptsb rptsb lowb highb] /=.
have [/eqP <-|/eqP anb] := boolP(lptsa == lptsb).
  have [/eqP <-|/eqP anb] := boolP(rptsa == rptsb).
    have [/eqP <-|/eqP anb] := boolP(lowa == lowb).
      have [/eqP <-|/eqP anb] := boolP(higha == highb).
        by apply:ReflectT.
      by apply : ReflectF => [][].
    by apply : ReflectF => [][].
  by apply: ReflectF=> [][].
by apply: ReflectF=> [][].
Qed.

Canonical cell_eqType := EqType cell (EqMixin cell_eqP).

Record event := Bevent {point : pt; outgoing : seq edge}.

Definition event_eqb (ea eb : event) : bool :=
  let: Bevent pta outa := ea in
  let: Bevent ptb outb := eb in
  (pta == ptb) && (outa == outb).

Lemma event_eqP : Equality.axiom event_eqb.
Proof.
rewrite /Equality.axiom.
move => [pta outa] [ptb outb] /=.
have [/eqP <-|/eqP anb] := boolP(pta == ptb).
  have [/eqP <-|/eqP anb] := boolP(outa == outb).
    by apply:ReflectT.
  by apply : ReflectF => [][].
by apply: ReflectF=> [][].
Qed.

Canonical event_eqType := EqType event (EqMixin event_eqP).

(* As in insertion sort, the add_event function assumes that event are
  sorted in evs (lexicographically, first coordinate, then second coordinate
  of the point.  On the other hand, no effort is made to sort the various
  edges in each list.  *)
Fixpoint add_event (p : pt) (e : edge) (inc : bool) (evs : seq event) :
  seq event :=
  match evs with
  | nil => if inc then [:: Bevent p [::]]
           else [:: Bevent p [:: e]]
  | ev1 :: evs' =>
    let p1 := point ev1 in
    if p == p1 then
      if inc then Bevent p1 (outgoing ev1) :: evs'
      else Bevent p1 (e :: outgoing ev1) :: evs' else
    if p_x p < p_x p1 then
      if inc then
        Bevent p [::] :: evs else
        Bevent p [:: e] :: evs
    else if (p_x p == p_x p1) && (p_y p < p_y p1) then
       if inc then
         Bevent p [::] :: evs else
         Bevent p [:: e] :: evs else
    ev1 :: add_event p e inc evs'
  end.

Lemma add_event_step (p : pt) (e : edge) (inc : bool) (evs : seq event) :
  add_event p e inc evs =
  match evs with
  | nil => if inc then [:: Bevent p [::]]
           else [:: Bevent p [:: e]]
  | ev1 :: evs' =>
    let p1 := point ev1 in
    if p == p1 then
      if inc then Bevent p1 (outgoing ev1) :: evs'
      else Bevent p1 (e :: outgoing ev1) :: evs' else
    if p_x p < p_x p1 then
      if inc then
        Bevent p [::] :: evs else
        Bevent p [:: e] :: evs
    else if (p_x p == p_x p1) && (p_y p < p_y p1) then
       if inc then
         Bevent p [::] :: evs else
         Bevent p [:: e] :: evs else
    ev1 :: add_event p e inc evs'
  end.
Proof. by case: evs. Qed.

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

Definition valid_cell c x := valid_edge (low c) x /\ valid_edge (high c) x.

(* Definition right_form (c : cell) : bool := low c <| high c. *)

Lemma order_edges_viz_point c p :
valid_edge (low c) p -> valid_edge (high c) p ->
(low c) <| (high c) ->
p <<= (low c) -> p <<= (high c).
Proof. apply : order_edges_viz_point'. Qed.

Lemma order_edges_strict_viz_point c p :
valid_edge (low c) p -> valid_edge (high c) p ->
(low c) <| (high c) ->
p <<< (low c) ->  p <<< (high c).
Proof. apply: order_edges_strict_viz_point'. Qed.

Definition dummy_pt := Bpt (0:R) 0.
Definition dummy_event := Bevent dummy_pt [::].
Definition dummy_edge : edge := (@Bedge  _ dummy_pt (Bpt (1:R) 0) ltr01).
Definition dummy_cell : cell := (@Bcell  (dummy_pt::[::]) (dummy_pt::[::]) dummy_edge dummy_edge).

Definition head_cell (s : seq cell) := head dummy_cell s.
Definition last_cell (s : seq cell) := last dummy_cell s.

(* if a cell doesn't contain a point, then either both edges are strictly under p or strictly over p *)
Definition contains_point (p : pt) (c : cell)  : bool :=
   ~~  (p <<< low c) && (p <<= (high c)).

Definition open_limit c :=
  min (p_x (right_pt (low c))) (p_x (right_pt (high c))).

Definition left_limit (c : cell) :=
  p_x (last dummy_pt (left_pts c)).

Definition right_limit c := p_x (last dummy_pt (right_pts c)).

Definition inside_open_cell p c :=
  [&& contains_point p c & left_limit c <= p_x p <= open_limit c].

Definition inside_closed_cell p c :=
  contains_point p c && (left_limit c <= p_x p <= right_limit c).

(* this function removes consecutives duplicates, meaning the seq needs to be sorted first if we want to remove all duplicates *)
Fixpoint no_dup_seq (A : eqType) (s : seq A) : (seq A) :=
  match s with
  | [::] => [::]
  | a::q => match q with
            | [::] => s
            | b::r => if a == b then no_dup_seq q else a::(no_dup_seq q)
            end
    end.

Fixpoint closing_rest (p: pt) (rest : seq cell) : (seq cell) :=
    match rest with
       | [::] => [::]
       | [:: c] => let op1 := vertical_intersection_point p (high c) in
                    match op1 with
                       | None => [::]
                       | Some(p1) =>
                        Bcell  (left_pts c) (no_dup_seq [:: p; p1]) (low c) (high c)::[::]
                    end
       | c::q =>  Bcell  (left_pts c) [::p] (low c) (high c)::closing_rest p q
    end.

Definition inspect [A : Type](a : A) : {x : A | a = x}.
exists a; apply: erefl.  
Defined.

Lemma closing_rest_ind
  (p : pt) (P : seq cell -> seq cell -> Prop) (rest : seq cell)
  (V1 : P nil nil)
  (V2 : forall c, vertical_intersection_point p (high c) = None ->
        P [:: c] [::])
  (V3 : forall c p1, vertical_intersection_point p (high c) = Some p1 ->
           P [:: c] [:: Bcell (left_pts c)
                             (no_dup_seq [:: p; p1]) (low c) (high c)])
  (V4 : forall (c : cell) (a : cell) (q : seq cell),
        (P (a :: q) (closing_rest p (a :: q)) ->
     (P (c :: a:: q) 
        (Bcell (left_pts c) [::p] (low c) (high c) ::
           closing_rest p (a :: q)))))
  :
  P rest (closing_rest p rest).
revert rest.
fix aux 1.
intros rest; case rest;[ | intros c q].
  exact V1.
destruct q as [ | a q'] eqn:A.
  destruct (inspect (vertical_intersection_point p (high c))) as [[p1 | ] h].
    simpl; rewrite h; exact (V3 c p1 h).
    simpl; rewrite h; exact (V2 c h).
  simpl. rewrite -[X in (Bcell _ _ _ _ :: X)]/(closing_rest p (a :: q')).
apply: V4; rewrite -A; exact (aux q).
Qed.

Definition closing_cells (p : pt) (contact_cells: seq cell) : (seq cell) :=
    match contact_cells with
      | [::] => [::]
      | [:: only_cell] =>
                      let op0 := vertical_intersection_point p (low only_cell) in
                      let op1 := vertical_intersection_point p (high only_cell) in
                      match (op0,op1) with
                          |(None,_) |(_,None)=> [::]
                          |(Some(p0),Some(p1)) =>
                              Bcell  (left_pts only_cell) (no_dup_seq [:: p0; p; p1])(low only_cell) (high only_cell)::[::]
                      end
      | c::q => match vertical_intersection_point p (low c) with
                | None => [::]
                | Some(p0) =>
                   Bcell  (left_pts c) (no_dup_seq [:: p0; p])
                           (low c) (high c) :: (closing_rest p q)
                end
    end.

Variant list_position := SINGLE | HEAD | MIDDLE | LAST.

Definition build_right_pts (v : list_position) (p pbot ptop : pt) :=
  match v with
  | SINGLE => no_dup_seq [:: pbot; p; ptop]
  | HEAD => no_dup_seq [:: pbot; p]
  | MIDDLE => [:: p]
  | LAST => no_dup_seq [:: p; ptop]
  end.

Definition close_cell (v : list_position)(p : pt)(c : cell) :=
  match vertical_intersection_point p (low c),
        vertical_intersection_point p (high c) with
  | None, _ | _, None => c
  | Some p1, Some p2 => 
    Bcell (left_pts c) (build_right_pts v p p1 p2) (low c) (high c)
  end.

Lemma close_cell_preserve_3sides v p c :
  [/\ low (close_cell v p c) = low c,
      high (close_cell v p c) = high c &
      left_pts (close_cell v p c) = left_pts c].
Proof.
rewrite /close_cell.
case: (vertical_intersection_point p (low c))=> [p1 | ] //.
by case: (vertical_intersection_point p (high c))=> [p2 | ].
Qed.

(* at each step we create the cell under the first outgoing edge and when there's only one left,
we create the two last cells *)
Fixpoint opening_cells_aux (p : pt) (out : seq edge) (low_e : edge) 
  (high_e : edge) : (seq cell) :=
      match out with
    | [::] => let op0 := vertical_intersection_point p low_e in
              let op1 := vertical_intersection_point p high_e in
                      match (op0,op1) with
                          |(None,_) |(_,None)=> [::]
                          |(Some(p0),Some(p1)) =>
                              (Bcell  (no_dup_seq ([:: p1; p; p0])) [::] low_e high_e) ::[::]
                      end
    | c::q => let op0 := vertical_intersection_point p low_e in
                    match op0 with
                       | None => [::]
                       | Some(p0) =>
                        (Bcell  (no_dup_seq([:: p; p0])) [::] low_e c) :: opening_cells_aux p q c high_e
                    end
end.

Definition opening_cells p out :=
   opening_cells_aux p (sort (@edge_below R) out).

Lemma opening_cells_left p out le he :
  {in opening_cells p out le he, forall c, left_limit c = p_x p}.
Proof.
rewrite /opening_cells.
elim: (sort _ _) le => [ | g1 gs Ih] le c.
  rewrite /=.
  case ple_eq : (vertical_intersection_point p le) => [ a | // ].
  case phe_eq : (vertical_intersection_point p he) => //.
  move: ple_eq=> /intersection_on_edge => -[] _ pxeq.
  by case: ifP=> _; case: ifP => _; rewrite inE /left_limit => /eqP ->.
rewrite /=.
case ple_eq : (vertical_intersection_point p le) => [ a | // ].
move: ple_eq=> /intersection_on_edge => -[] _ pxeq.
by case: ifP => _ //; rewrite inE => /orP[/eqP -> | /Ih].
Qed.

Fixpoint open_cells_decomposition_contact open_cells pt contact high_e : seq cell * seq cell * edge :=
match open_cells with
        | [::] => (contact, [::], high_e)
        | Bcell lpt rpt low high :: q  =>
                if (contains_point pt (Bcell lpt rpt low high)) then
                    open_cells_decomposition_contact q pt (rcons contact (Bcell lpt rpt low high)) high
                else (contact, open_cells, high_e)
        end.

Fixpoint open_cells_decomposition_fix open_cells pt first_cells : seq cell * seq cell * seq cell * edge * edge :=

match open_cells with
        | [::] => (first_cells, [::], [::], dummy_edge, dummy_edge)
        | Bcell lpt rpt low high :: q  =>
            if (contains_point pt (Bcell lpt rpt low high)) then
                   let '(contact, last_cells, high_e) := open_cells_decomposition_contact q pt [::] high in
                   (first_cells, (Bcell lpt rpt low high)::contact,last_cells, low, high_e)
            else open_cells_decomposition_fix q pt (rcons first_cells ( Bcell lpt rpt low high))
end.

(* only works if cells are sorted *)
Definition open_cells_decomposition (open_cells : seq cell) (p : pt) : seq cell * seq cell * seq cell * edge * edge :=
  match open_cells with
    | [::] => ([::],[::],[::], dummy_edge, dummy_edge)
    | _  => open_cells_decomposition_fix open_cells p [::]
  end.

Definition step (e : event) (open_cells : seq cell) (closed_cells : seq cell) : (seq cell) * (seq cell) :=
   let p := point e in
   let '(first_cells, contact_cells, last_cells, lower_edge, higher_edge) := open_cells_decomposition open_cells p in
   let closed := closing_cells p contact_cells in
   let closed_cells := closed_cells++closed in
   let new_open_cells :=
     opening_cells p (outgoing e) lower_edge higher_edge in
   (first_cells++new_open_cells++last_cells, closed_cells).

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

Fixpoint scan (events : seq event) (open_cells : seq cell)
  (closed_cells : seq cell) : seq cell * seq cell :=
  match events with
     | [::] => (closed_cells, open_cells)
     | e::q => let (open, closed) := (step e open_cells closed_cells) in  scan q open closed
  end.

Definition start (events : seq event) (bottom : edge) (top : edge) :
  seq cell * seq cell :=
  scan events [:: Bcell (leftmost_points bottom top) [::] bottom top] [::].

Section proof_environment.
Variable bottom top : edge.

Definition lexPtEv (e1 e2 : event) : bool :=
  lexPt (point e1) (point e2).

Definition inside_box p :=
(~~ (p <<= bottom)  && (p <<< top) ) &&
  ((p_x (left_pt bottom) < p_x p < p_x (right_pt bottom)) &&
  (p_x (left_pt top) < p_x p < p_x (right_pt top))).

Lemma inside_box_valid_bottom_top p g :
  inside_box p ->
  g \in [:: bottom; top] -> valid_edge g p.
Proof.
move=>/andP[] _ /andP[] /andP[] /ltW a /ltW b /andP[] /ltW c /ltW d.
by rewrite /valid_edge !inE=> /orP[] /eqP ->; rewrite ?(a, b, c, d).
Qed.

Definition event_close_edge ed ev : bool :=
right_pt ed == point ev.

Definition end_edge edge events : bool :=
(edge \in [:: bottom; top]) || has (event_close_edge edge) events.

Definition close_alive_edges open future_events : bool :=
all (fun c => (end_edge (low c) future_events) && (end_edge (high c) future_events)) open.

Definition close_out_from_event ev future : bool :=
  all (fun edge => end_edge edge future) (outgoing ev).

Fixpoint close_edges_from_events events : bool :=
  match events with
  | [::] => true
  | ev :: future_events => close_out_from_event ev future_events && close_edges_from_events future_events
  end.

Lemma close_edges_from_events_step events :
  close_edges_from_events events = match events with
  | [::] => true
  | ev :: future_events => close_out_from_event ev future_events && close_edges_from_events future_events
  end.
Proof. by case: events. Qed.

Lemma insert_opening_all (first_cells  new_open_cells last_cells : seq cell) p :
all p first_cells  -> all p new_open_cells  ->
  all p last_cells  -> all p (first_cells++new_open_cells++ last_cells).
Proof.
move => C_first C_new C_last.
 rewrite  all_cat all_cat.
apply /andP.
split.
  by [].
apply /andP.
split.
  by [].
by [].
Qed.

Lemma insert_opening_closeness first_cells new_open_cells last_cells events :
  close_alive_edges first_cells events -> close_alive_edges new_open_cells events ->
  close_alive_edges last_cells events -> close_alive_edges (first_cells++new_open_cells++ last_cells) events.
Proof.
apply insert_opening_all.
Qed.

Lemma lexPtEv_trans : transitive lexPtEv.
Proof. by move=> e2 e1 e3; rewrite /lexPtEv; apply: lexPt_trans. Qed.

Lemma open_cells_decomposition_contact_eq open pt contact high_e:
open_cells_decomposition_contact open pt contact high_e =
match open with
        | [::] => (contact, [::], high_e)
        | Bcell lpt rpt low high :: q  =>
                if (contains_point pt (Bcell lpt rpt low high)) then
                    open_cells_decomposition_contact q pt (rcons contact (Bcell lpt rpt low high)) high
                else (contact, open, high_e)
        end.
Proof.
  by case : open.
Qed.

Lemma rcons_neq0 (A : Type) (z : A) (s : seq A) : (rcons s z) <> nil.
Proof.
by case : s.
Qed.

Lemma h_c_contact open_cells pt high_e contact_cells :
forall contact last_c high_c,
open_cells_decomposition_contact open_cells pt contact_cells high_e =(contact,last_c, high_c) ->
((high (last dummy_cell contact) == high_c) && (contact != nil)) || ((contact == contact_cells) && (high_e == high_c)).
Proof.
elim : open_cells contact_cells high_e => [//= | c open Ih] contact_cells high_e contact_c last_c high_c.
  move => H.
  inversion H.
  by rewrite ! eqxx orbT.
rewrite /=.
case : c => [lpts rpts lowc highc].
case : ifP => [contain| notcontain].
  case h : (open_cells_decomposition_contact _ _ _ _) => [[contact lc]high_final].
  move : (Ih _ _ _ _ _ h).
  move =>  /orP [ /andP [] /eqP <-// cnnil|].
    move => [] <- Hlc -> .
    by rewrite eqxx cnnil.
  move  => /andP [/eqP tmp2 /eqP tmp3].
  move => [] <- Hlc Hhc .
  rewrite tmp2 .
  rewrite last_rcons /=  tmp3 Hhc eqxx andTb .
  apply /orP; left.
  apply /eqP /rcons_neq0.
move => [] -> _ -> .
by rewrite !eqxx orbT.
Qed.

Lemma l_h_c_fix open_cells pt fc:
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition_fix open_cells pt fc = (first_cells, contact, last_cells, low_f, high_f)   ->
(exists c, (c \in open_cells) /\ (contains_point pt c)) ->
(low (head dummy_cell contact) == low_f) /\ (high (last dummy_cell contact) == high_f) /\ contact != nil.
Proof.
  move => f_c c_c l_c lowf highf.
rewrite /=.
elim : open_cells fc => [/= | c q IH] fc.
  move =>   _ /= [] x.
   rewrite in_nil.
   move => /andP.
   by rewrite andFb.

rewrite /=.
case : c => [lpts rpts lowfi highfi].
case : ifP => [contain |notcontain].

  case h : (open_cells_decomposition_contact _ _ _ _) => [[contact last_c] high_c].
  move => [] _ <- _ <- <- /= exi.
  rewrite eqxx.
  have tmp := h_c_contact h.
  move : tmp => /orP [/andP [/eqP higheq cnnil]| /andP [/eqP cnil /eqP higheq]].
    rewrite -higheq /=.

     case : contact h higheq cnnil.
        by [].
        rewrite //=.

  rewrite cnil higheq.

  by rewrite eqxx.
move /IH.
move => IH' exi.
apply IH'.
move : exi => [] x [xin xcontains].
rewrite inE in xin .
move : xin => /orP [ /eqP xeqp | xinq2].
  rewrite -xeqp in notcontain.
  by rewrite notcontain in xcontains.
by exists x.
Qed.

Definition adj_rel := [rel x y : cell | high x == low y].

Definition adjacent_cells := sorted adj_rel.

Lemma adjacent_catW s1 s2 : 
  adjacent_cells (s1 ++ s2) -> adjacent_cells s1 /\ adjacent_cells s2.
Proof.
case: s1 => [ // | cs1  s1 /=]; rewrite /adjacent_cells.
rewrite cat_path => /andP[] -> ps2; split=> //.
by move/path_sorted: ps2.
Qed.

Lemma adjacent_cut l2 a lc :
l2 != nil ->
((high (last dummy_cell l2) == low a) &&
adjacent_cells l2 &&
adjacent_cells (a::lc) ) =
adjacent_cells (l2 ++ a::lc).
Proof.
case : l2 => [//= | c2 q2 _].
elim : q2 c2 => [ | c3 q3 IH]  c2 //=.
by rewrite andbT.
have /= IH' := IH c3.
rewrite andbCA.
rewrite -IH'.
by rewrite !andbA.
Qed.

Lemma l_h_c_decomposition open_cells pt :
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition open_cells pt  = (first_cells, contact, last_cells, low_f, high_f)   ->
(exists c, (c \in open_cells) /\ (contains_point pt c)) ->
(low (head dummy_cell contact) == low_f) /\ (high (last dummy_cell contact) == high_f) /\ contact != nil .
Proof.
rewrite /=.
case :  open_cells  => [/= | c q] fc c_c lc low_f high_f.
move => [] _ <- _ _ _ []x.
rewrite in_nil.
  move => /andP.
  by rewrite andFb.

rewrite /open_cells_decomposition .
move => h.
by have  := (l_h_c_fix h).
Qed.

Definition edge_above_vert (e1 : edge) (e2 : edge) : bool :=
let: Bedge a1 b1 p1 := e1 in
let: Bedge a2 b2 p2 := e2 in
let maxleft := max (p_x a1) (p_x  a2) in
let minright := min (p_x b1) (p_x  b2) in
match vertical_intersection_point (Bpt maxleft 0) e1 with
 | None => false
 | Some(p) =>
  match vertical_intersection_point (Bpt minright 0) e1 with
    |None => false
    | Some(p2) =>
  (p <<= e2) && (p2 <<= e2)
  end
end.

Definition bottom_edge_seq_above (s : seq cell) (p : pt) :=
  if s is c :: _ then (p) <<= (low c) else true.

Definition bottom_edge_seq_below (s : seq cell) (p : pt) :=
  if s is c :: _ then ~~ (p <<< low c) else true.

Lemma strict_under_cell (c : cell) (p : pt) :
  valid_cell c p ->
  low c <| high c -> p <<= (low c) -> ~~ contains_point p c ->
  p <<< (low c).
Proof.
move=> valcp rfc.
move: (valcp)=> [vallp valhp].
rewrite (under_onVstrict vallp) => /orP [] //.
move=> ponl; rewrite /contains_point negb_and negbK=> /orP[] //.
case/negP.
apply: (order_edges_viz_point vallp) => //.
by rewrite under_onVstrict // ponl.
Qed.

Definition s_right_form (s : seq cell)  : bool :=
  all (fun c => low c <| high c ) s.

Lemma opening_cells_seq_edge_shift p oe le he :
  {in oe, forall g, left_pt g == p} ->
  valid_edge le p -> valid_edge he p ->
  le :: [seq high i | i <- opening_cells_aux p oe le he] =
  rcons [seq low i | i <- opening_cells_aux p oe le he] he.
Proof.
move=> + + vh.
elim: oe le => [ | g oe Ih] le leftg vl.
  rewrite /=; case: (exists_point_valid vl) => [p1 ->].
  by case: (exists_point_valid vh) => [p2 ->].
rewrite /=; case: (exists_point_valid vl) => [p1 ->] /=.
rewrite Ih //; last first.
  have gin : g \in g :: oe by rewrite inE eqxx.
  have := @valid_edge_extremities R g p; rewrite (eqP (leftg g gin)) eqxx.
  by apply.
by move=> g' gin; apply: leftg; rewrite inE gin orbT.
Qed.

Lemma opening_cells_aux_subset c p s le he:
  c \in opening_cells_aux p s le he ->
  (low c \in le :: s) && (high c \in he :: s).
Proof.
elim: s le => [ | ed s Ih] le /=.
by do 2 case: (vertical_intersection_point p _) => [? | //];
  rewrite !inE => /eqP -> /=; rewrite !eqxx.
case: (vertical_intersection_point p le) => [p' | //].
rewrite !inE=> /orP[/eqP -> /=| ]; rewrite ?eqxx ?orbT //.
move=> /Ih /andP[]; rewrite !inE=> ->; rewrite ?orbT /= orbCA => ->.
by rewrite orbT.
Qed.

Lemma opening_cells_subset c p s le he :
  c \in opening_cells p s le he ->
  (low c \in le :: s) && (high c \in he :: s).
Proof.
move=> cin.
have:= opening_cells_aux_subset cin.
by rewrite !inE !(perm_mem (permEl (perm_sort _ _))).
Qed.

Lemma opening_cells_aux_nnil p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  opening_cells_aux p s le he != nil.
Proof.
by move=> + vhe; case: s => [ | g1 s] vle lsp; rewrite /= pvertE // ?pvertE.
Qed.

Lemma opening_cells_aux_high p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  [seq high i | i <- opening_cells_aux p s le he] = rcons s he.
Proof.
move=> vle vhe lsp.
elim: s le vle lsp => [ | g1 s Ih] le vle lsp.
  by rewrite /= pvertE // pvertE.
rewrite /= pvertE //= Ih //.
  by rewrite -(eqP (lsp g1 _)) ?inE ?valid_edge_extremities ?eqxx.
by move=> g2 g2in; apply: lsp; rewrite inE g2in orbT.
Qed.

Lemma opening_cells_high p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  [seq high i | i <- opening_cells p s le he] =
  rcons (sort (@edge_below R) s) he.
Proof.
move=> vle vhe lsp; rewrite /opening_cells.
rewrite opening_cells_aux_high => //.
by move=> g; rewrite mem_sort; apply: lsp.
Qed.

Lemma opening_cells_aux_right_form (ctxt s : seq edge) (p : pt) low_e high_e :
p >>= low_e -> p <<< high_e -> valid_edge high_e p ->
low_e \in ctxt -> high_e \in ctxt ->
low_e <| high_e -> {in s, forall g, left_pt g == p} ->
{in ctxt &, (@no_crossing R)} ->
{subset s <= ctxt} ->
path (@edge_below R) low_e s  ->
s_right_form (opening_cells_aux p s low_e high_e).
Proof.
move=> + ph vh + hin + + noc + +.
elim: s low_e => [ | g1 edges IH] low_e
  pabove lin lowhigh outs allin sorted_e /=.
  case v_i_l_eq : (vertical_intersection_point p low_e)=> [a1 | ]; last by [].
  case v_i_h_eq : (vertical_intersection_point p high_e) => [a2 | ]; last by [].
  by case: ifP => [a2e | a2ne]; case: ifP => [a1e | a1ne]; rewrite /= ?andbT.
case v_i_l_eq :
   (vertical_intersection_point _ low_e)=> [a1 | ]; last by [].
have outs' : {in edges, forall g, left_pt g == p}.
  by move=> g gin; apply outs; rewrite inE gin orbT.
have allin' : {subset edges <= ctxt}.
  by move=> g gin; rewrite allin // inE gin orbT.
have sorted_e' : path (@edge_below R) g1 edges.
   by apply: (path_sorted sorted_e).
have /eqP gl : left_pt g1 == p by rewrite outs // inE eqxx.
have g1belowhigh : g1 <| high_e.
  have gin' : g1 \in ctxt by rewrite allin // inE eqxx.
  have/no_crossingE := noc g1 high_e gin' hin.
  by rewrite gl=>/(_ vh)=> -[]/(_ ph).
have pong : p === g1 by rewrite -gl left_on_edge.
have paboveg1 : p >>= g1
   by rewrite strict_nonAunder ?pong //; case/andP: pong.
move: (sorted_e) => /=/andP[] low_eg1 _.
have g1in : g1 \in ctxt by rewrite allin // inE eqxx.
by rewrite low_eg1; apply: (IH g1).
Qed.

Lemma opening_cells_right_form p s low_e high_e :
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
move=> vh pabove punder lowhigh outs alla allb noc; apply/allP.
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
have it := (opening_cells_aux_right_form _ _ _ lin hin lowhigh outs).
by apply: (allP (it _ _ _ _ _ _) x xin).
Qed.

Definition seq_valid (s : seq cell) (p : pt) : bool :=
    all (fun c => (valid_edge (low c) p) && (valid_edge (high c) p)) s.

Lemma seq_valid_high (s : seq cell) (p : pt) :
  seq_valid s p -> {in [seq high i | i <- s], forall g, valid_edge g p}.
Proof.
by move=> sval g /mapP [c cin ->]; move: (allP sval c cin)=> /andP[].
Qed.

Lemma seq_valid_low (s : seq cell) (p : pt) :
  seq_valid s p -> {in [seq low i | i <- s], forall g, valid_edge g p}.
Proof.
by move=> sval g /mapP [c cin ->]; move: (allP sval c cin)=> /andP[].
Qed.

Lemma insert_opening_valid first_cells new_open_cells last_cells p :
seq_valid first_cells p -> seq_valid  new_open_cells p ->
seq_valid last_cells p -> seq_valid  (first_cells++new_open_cells++ last_cells) p.
Proof.
apply insert_opening_all.
Qed.

Lemma closing_cell1 p c :
  seq_valid [:: c] p ->
  closing_cells p [:: c] = [:: close_cell SINGLE p c].
Proof.
rewrite /close_cell/build_right_pts/= => /andP[] /andP[] vl vh _.
have [p1 p1q] := (exists_point_valid vl); rewrite p1q.
by have [p2 p2q] := (exists_point_valid vh); rewrite p2q.
Qed.

Definition cutlast (T : Type) (s : seq T) :=
match s with | a :: s => belast a s | [::] => [::] end.

Lemma closing_rest_map dummy p s :
  (0 < size s)%N ->
  seq_valid s p ->
  closing_rest p s =
  rcons (map (close_cell MIDDLE p) (cutlast s))
   (close_cell LAST p (last dummy s)).
Proof.
pattern s, (closing_rest p s); apply:(@closing_rest_ind p) => //.
- by move=> c abs sz /andP[] /andP[] vl /exists_point_valid [?]; rewrite abs.
- rewrite /close_cell/build_right_pts/cutlast/=; move=> c p1 /[dup] vip1 ->.
  by move=> _ /andP[] /andP[] /exists_point_valid [p2 ->].
move=> c a q Ih _ /= /andP[] /andP[]vl vh sv; congr (_ :: _).
  rewrite /close_cell; have [p1 ->] := exists_point_valid vl.
  by have [p2 ->] := exists_point_valid vh.
by rewrite -[LHS]/(closing_rest p (a :: q)); apply: Ih.
Qed.

Lemma closing_cells_map p s :
  (1 < size s)%N ->
  seq_valid s p ->
  closing_cells p s =
  close_cell HEAD p (head dummy_cell s) ::
  rcons (map (close_cell MIDDLE p) (cutlast (behead s)))
   (close_cell LAST p (last dummy_cell s)).
Proof.
case: s => [ // | c [ // | a s]] _.
rewrite /seq_valid allcons -/(seq_valid (a :: s) p)=> /andP[]/andP[]vl vh vs.
rewrite /= [close_cell _ _ _ as X in (X :: _)]/close_cell.
have [p1 ->] := exists_point_valid vl.
have [p2 ->] := exists_point_valid vh; congr (_ :: _).
by rewrite -[LHS]/(closing_rest p (a :: s)); apply: (closing_rest_map a).
Qed.

Lemma strict_under_seq p c q :
  adjacent_cells (c :: q) ->
  seq_valid (c :: q) p ->
  s_right_form (c :: q) ->
  p <<< (low c) ->
  forall c1, c1 \in q -> p <<< (low c1).
Proof.
elim: q c => [// | c' q Ih] c adj vals rfs plow c1 c1in.
move: adj; rewrite /adjacent_cells /= => /andP[/eqP eq_edges adj'].
move: vals; rewrite /seq_valid /= => /andP[/andP[vallc valhc] valc'q].
move: rfs; rewrite /s_right_form /= => /andP[lowhigh rfc'q].
have pc' : p <<< (low c').
  by rewrite -eq_edges; apply: (order_edges_strict_viz_point vallc).
have [/eqP c1c' | c1nc'] := boolP (c1 == c').
  by rewrite c1c'.
apply: (Ih c')=> //.
  by move: c1in; rewrite !inE (negbTE c1nc').
Qed.

Lemma strict_under_seq' p c q :
  adjacent_cells (c :: q) ->
  seq_valid (c :: q) p ->
  s_right_form (c :: q) ->
  p <<< (low c) ->
  forall c1, c1 \in (c :: q) -> p <<< (low c1).
Proof.
move=> adj sv rf pl c1; rewrite inE=> /orP[/eqP -> // | ].
by apply: (strict_under_seq adj sv rf pl).
Qed.

Lemma contact_preserve_cells open_cells pt high_e contact_cells :
forall contact last_c high_c,
open_cells_decomposition_contact open_cells pt contact_cells high_e = (contact, last_c, high_c) ->
contact_cells ++ open_cells == contact ++ last_c.
Proof.
elim : open_cells contact_cells high_e => [/=| c q  IH] contact_cells high_e contact last_c high_c.
  move =>  [] -> <- _.
  by rewrite eqxx.
case : c => [lpts rpts lowc highc].
rewrite /=.
case : ifP => [contain| notcontain].
  case h : (open_cells_decomposition_contact _ _ _ _)=> [[contact1 last_c1] high_c1].
  move =>  [] <- <- _.
  have h2: ((rcons contact_cells {| left_pts := lpts; right_pts := rpts;low := lowc; high := highc |}) ++ q == contact1 ++ last_c1) .
    apply (IH _ highc _ _ high_c1).
    by rewrite h.
  move : h2 => /eqP  h2.
  rewrite -h2.
  by rewrite cat_rcons eqxx.
move =>  [] -> -> _.
by rewrite eqxx.
Qed.

Lemma fix_preserve_cells open_cells pt fc :
forall first_cells contact last_cells low high_f,
open_cells_decomposition_fix open_cells pt fc = (first_cells, contact, last_cells, low, high_f) ->
fc ++ open_cells == first_cells ++ contact ++ last_cells.
Proof.
elim : open_cells fc => [/=| c q IH] fc first_cells contact last_cells low_f high_f.
  move =>  [] <- <- <- _ _ .
  by [].
case : c => [lpts rpts lowc highc].
rewrite /=.
case : ifP => [contain| notcontain].
  case h : (open_cells_decomposition_contact _ _ _ _) => [[contact0 last_c0] high_c0].
  move =>  [] -> <- <- -> _.
  by have /= /eqP -> := (contact_preserve_cells h) .
move => h.
have /eqP <- := (IH _ _ _ _ _ _ h).
by rewrite cat_rcons.
Qed.

Lemma decomposition_preserve_cells open_cells pt :
forall first_cells contact last_cells low high_f,
open_cells_decomposition open_cells pt  = (first_cells, contact, last_cells, low, high_f) ->
open_cells = first_cells ++ contact ++ last_cells .
Proof.
case :  open_cells  => [/= | c q] fc c_c lc low_f high_f.
  by move => [] <- <- <- _ _.
rewrite /open_cells_decomposition.
move => h.
by have /= /eqP <- := (fix_preserve_cells h).
Qed.

Lemma close_imp_cont c e :
low c <| high c ->
valid_edge (low c) (point e) /\ valid_edge (high c) (point e) ->
event_close_edge (low c) e \/  event_close_edge (high c) e->
contains_point (point e) c.
Proof.
rewrite /contains_point /event_close_edge .
move =>  rf val [/eqP rlc | /eqP rhc].
move : rf val.
  rewrite /point_strictly_under_edge -rlc {rlc e}.
  have := (pue_formula_two_points (right_pt (low c)) (left_pt (low c))) => [][] _ [] /eqP -> _ .
  rewrite lt_irreflexive /=.
  rewrite /edge_below.
  move => /orP [] /andP [] //= => pablhlow pabrhlow [] _ validrlhigh.
  apply: not_strictly_above pablhlow pabrhlow validrlhigh.
  move : rf val.
rewrite /point_under_edge -rhc {rhc}.
have := (pue_formula_two_points (right_pt (high c)) (left_pt (high c))) => [] [] _ [] /eqP -> _ /=.
rewrite le_refl /edge_below /= andbT=> /orP [] /andP [] //= => pablhlow pabrhlow [] valrhlow _ .
apply : not_strictly_under pablhlow pabrhlow valrhlow.
Qed.

Lemma contrapositive_close_imp_cont c e :
low c <| high c->
valid_edge (low c) (point e) /\ valid_edge (high c) (point e) ->
~ contains_point (point e) c ->
~ event_close_edge (low c) e /\ ~ event_close_edge (high c) e.
Proof.
  move => rf val ev.
have aimpb := (close_imp_cont rf val).
have  := (contra_not  ( contains_point (point e) c) (event_close_edge (low c) e \/ event_close_edge (high c) e) aimpb ev) .
move => /orP /= .
rewrite negb_or.
by move => /andP [] /negP a /negP.
Qed.

Lemma adjacent_cons a q : adjacent_cells (a :: q) -> adjacent_cells q.
Proof.
by rewrite /=; case: q => [// | b q]; rewrite /= => /andP[].
Qed.

Lemma contact_last_not_contain open_cells p high_e contact_cells :
bottom_edge_seq_above open_cells p ->
s_right_form open_cells ->
seq_valid open_cells p ->
adjacent_cells open_cells ->
forall contact last_c high_c, 
open_cells_decomposition_contact open_cells p contact_cells high_e =
   (contact, last_c, high_c) ->
forall c, (c \in last_c) -> ~ contains_point p c.
Proof.
move => ba oprf opvalid  adj_op c_c last_cells highc.
elim op : open_cells ba oprf opvalid adj_op last_cells contact_cells high_e => [/= | c q  IH] ba op_rf opvalid adj_op last_c contact high_e.
  by move =>  [] _ <-  _  .
move => op_c.
have c_eq := (contact_preserve_cells op_c).
move : op_c.
case ceq : c => [lpts rpts lowc high_c].
rewrite /=.
case : ifP => [contain | /negbT notcontain].
  case h : (open_cells_decomposition_contact _ _ _ _)=> [[contact1 last_c1] high_c1].
  move =>  [] a  <- b.
  rewrite a b in h.
  have q_rf: s_right_form q.
    move : op_rf.
    by rewrite /s_right_form /all => /andP [] _.
  have qval : (seq_valid q p).
    move : opvalid.
    by rewrite /s_right_form /all => /andP [] _.
  have adjq : adjacent_cells q by apply: (adjacent_cons adj_op).
  have baq : bottom_edge_seq_above q p.
    move: contain; rewrite /contains_point /= => /andP[] _.
    rewrite /bottom_edge_seq_above; move: adj_op.
    by case: (q)=> //= a' q' => /andP[/eqP <- _]; rewrite ceq.
  by apply : (IH baq q_rf qval adjq last_c1 (rcons contact {| left_pts := lpts; right_pts := rpts;low := lowc; high := high_c |})  high_c h).
move =>  [] conteq lc heq {IH}.
rewrite -lc.
move => c1.
rewrite inE => /orP[ | c1inq].
  by move : notcontain => /negP notcontain /eqP  -> .
have rfc1 : low c1 <| high c1.
  move : op_rf.
  move =>  /allP /= incq /=.
  have := (incq c1).
  by rewrite inE c1inq orbT => // /(_ isT).
have valc1 : valid_edge (low c1) p /\ valid_edge (high c1) p.
  move : opvalid.
  rewrite /seq_valid.
  move =>  /allP /= valcq /=.
  have := (valcq c1).
  rewrite inE c1inq orbT.
  move =>  a.
  apply /andP.
by apply a. 
have [vallc valhc] : valid_edge (low c) p /\ valid_edge (high c) p.
  by move: opvalid => /allP /= /(_ c); rewrite inE eqxx => /(_ isT)=>/andP.
have lowhigh : (low c) <| (high c).
  by move: op_rf=> /allP /(_ c); rewrite inE eqxx  => /(_ isT).
have underhigh : p <<= (high_c).
  rewrite (_ : high_c = high c); last by rewrite ceq.
  by apply: order_edges_viz_point.
have strictunder : p <<< (low c).
  by move: notcontain; rewrite ceq negb_and /= underhigh orbF negbK.
rewrite /edge_below in rfc1.
move: notcontain; rewrite /contains_point negb_and negbK /==> notcontain.
apply/negP; rewrite negb_and negbK.
by rewrite (strict_under_seq adj_op opvalid op_rf strictunder).
Qed.

(* this lemma below is not true, see the counter example below.
Lemma lowest_above_all_above (s : seq cell) p :
s != [::] ->
adjacent_cells s ->
s_right_form s ->
 p <<< (low (head dummy_cell s)) ->
forall c, (c \in s) ->   p<<< (low c) /\  p <<< (high c) .
Proof.
case: s => [// | c q].
*)

Lemma lowest_above_all_above_counterexample :
  ~(forall (s : seq cell) p,
       s != [::] -> adjacent_cells s ->
       s_right_form s -> p <<< (low (head dummy_cell s)) ->
      forall c, (c \in s) ->   p<<< (low c) /\  p <<< (high c)).
Proof.
move=> abs.
set e1 := @Bedge R {|p_x := 0; p_y := 1|} {|p_x := 1; p_y := 1|} ltr01.
set e2 := @Bedge R {|p_x := 0; p_y := 2%:R|} {|p_x := 1; p_y := 1|} ltr01.
set p := {|p_x := (3%:R):R; p_y := 0|}.
set c := Bcell [::] [::] e1 e2.
have exrf : s_right_form [:: c].
  rewrite /= /= /e1 /e2 /edge_below /= /point_under_edge /=.
  rewrite /point_strictly_under_edge  /=.
  rewrite !(mul0r, subrr, mul1r, subr0, add0r, addr0, oppr0, opprK).
  rewrite le_refl lt_irreflexive /= !andbT.
  rewrite -[X in X - 2%:R]/(1%:R) -opprB -natrB //  -[(2-1)%N]/1%N.
  by rewrite lerN10.
have plow : p <<< low (head dummy_cell [:: c]).
  rewrite /point_strictly_under_edge  /=.
  by rewrite !(mul0r, subrr, mul1r, subr0, add0r, addr0, oppr0, opprK) ltrN10.
have := abs [::c] p isT isT exrf  plow c.
rewrite inE=> /(_ (eqxx _))=> [][] _.
rewrite /point_strictly_under_edge /=.
rewrite !(mul0r, subrr, mul1r, subr0, add0r, addr0, oppr0, opprK, mulr1).
rewrite (addrC (- _)) -natrM -!natrB // -[X in X%:R]/(1%N).
by rewrite ltNge ler0n.
Qed.

Lemma fix_first_cells_top_edge_below fc cells p :
adjacent_cells cells ->
bottom_edge_seq_below cells p ->
{in fc, forall c, p >>> high c} ->
forall fc' cc' lc' le he,
open_cells_decomposition_fix cells p fc = 
  (fc', cc', lc', le, he) ->
{in fc', forall c, p >>> high c}.
Proof.
elim: cells fc => [/= | c cells Ih] fc.
  by move=> _ _ known fc' cc' lc' le he [] <- _ _ _ _.
move=>/[dup]adj /adjacent_cons adj' /= above known.
case ceq : c => [lpts rpts lc hc].
rewrite -ceq; case ctp : (contains_point p c).
  case : (open_cells_decomposition_contact cells p [::] hc)
    => [[cc0 lc0] he0] /=.
  by move=> fc' cc' lc' le he [] <- _ _ _ _.
case rq : (open_cells_decomposition_fix cells p (rcons fc c)) =>
  [[[[fc'0 cc'0] lc'0] le0] he0].
move=> fc' cc' lc' le he [] <- _ _ _ _.
have btm : bottom_edge_seq_below cells p.
  move: adj ; rewrite /=; case: (cells) => [// | a cells'].
  move=> /andP[] /eqP hq _; move/negbT: ctp; rewrite negb_and above /=.
  by rewrite hq=> /underWC.
have addk : {in rcons fc c, forall c', p >>> high c'}.
  move=> x; rewrite mem_rcons inE => /orP[/eqP -> | xin]; last first.
    by apply: known.
  by move/negbT: ctp; rewrite negb_and above /=.
apply: (Ih _ adj' btm addk _ _ _ _ _ rq).
Qed.

Lemma fix_not_contain fc open_cells p   :
(forall c, c \in fc  -> ~ contains_point p c) ->
s_right_form open_cells ->
seq_valid open_cells p ->
adjacent_cells open_cells ->
bottom_edge_seq_below open_cells p ->
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition_fix open_cells p fc =
  (first_cells, contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) ->
~ contains_point p c.
Proof.
elim: open_cells fc => [/= | c1 open_cells IH] fc cfc.
  move=>_ _  _ _ fc' cc lc l_e h_e=> [][] <- _ <- _ _ c.
  by rewrite orbF; apply: cfc.
rewrite /bottom_edge_seq_below=> rfc1 valc1  adjc1 pabovec1 fc' cc lc l_e h_e.
rewrite /=.
case c1_eq : c1 => [lpts rpts lc1 hc1].
case open_cells_eq : open_cells => [ | c2 q] //.
  case: ifP => [contains | /negbT notcontains] /=.
    by move=> [] <- _ <- _ _ c; rewrite orbF; apply: cfc.
  move=> [] <- _ <- _ _ c; rewrite orbF -cats1 mem_cat => /orP[cinf |].
    by apply: cfc.
  rewrite inE => /eqP ->.
  by move : notcontains => /negP.

have rfo : s_right_form (c2 :: q).
  rewrite -open_cells_eq.
  by apply/allP=> c' c'in; apply (allP rfc1); rewrite inE c'in orbT.
have valo : seq_valid (c2 :: q) p.
  rewrite -open_cells_eq.
  by apply/allP=> c' c'in; apply: (allP valc1); rewrite inE c'in orbT.
move: (adjc1); rewrite open_cells_eq => /andP[/eqP c1c2 adjc2'].
have adjo : adjacent_cells (c2 :: q) by exact adjc2'.
case: ifP => [contains | /negbT notcontains].
  case contact_eq : 
  (open_cells_decomposition_contact (c2 :: q) p [::] hc1) =>
  [[contact_cells last_cells] edge1] [] <- _ <- _ _.
  move=> c /orP[cinfc | cinlc].
    by apply: cfc.
  have pundero : bottom_edge_seq_above (c2 :: q) p.
    by rewrite /= -c1c2 c1_eq; move: contains => /andP[] /=.
  by apply :  (contact_last_not_contain _ _ _ _ contact_eq).
have belowc2 : bottom_edge_seq_below (c2 :: q) p.
  move: notcontains; rewrite -c1_eq negb_and negbK (negbTE pabovec1) /=.
  by rewrite /= c1c2 => *; apply/underWC.
move=> fixeq.  
have := IH (rcons fc c1); rewrite open_cells_eq c1_eq.
move=> /(_ _ rfo valo adjo belowc2 _ _ _ _ _ fixeq); apply.
move=> c; rewrite -cats1 mem_cat inE=> /orP[cinfc | /eqP ->].
  by apply: cfc.
by move : notcontains => /negP.
Qed.

Lemma decomposition_not_contain open_cells p : 
forall first_cells contact last_cells low_f high_f,
s_right_form open_cells ->
seq_valid open_cells p ->
adjacent_cells open_cells ->
bottom_edge_seq_below open_cells p ->
open_cells_decomposition open_cells p  = (first_cells, contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) -> ~ contains_point p c.
Proof.
move => fc c_c l_c low_f high_f.
rewrite /open_cells_decomposition.
case: open_cells => [ | c q] rfo valo adjo boto.
  by move=>[] <- _ <- _ _ c.
by move/fix_not_contain; apply.
Qed.

Lemma decomposition_not_end open_cells e :
forall first_cells contact last_cells low_f high_f,
s_right_form open_cells ->
seq_valid open_cells (point e) ->
adjacent_cells open_cells ->
bottom_edge_seq_below open_cells (point e) ->
open_cells_decomposition open_cells (point e)  = (first_cells, contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) -> ( ~ event_close_edge (low c) e) /\ ( ~ event_close_edge (high c) e).
Proof.
move => fc c_c l_c low_f high_f srf svalid adj bedbelow dec_eq c1 c1nfclc .
have := (decomposition_not_contain srf svalid adj bedbelow dec_eq c1nfclc).
have c1open : c1 \in open_cells.
    rewrite (decomposition_preserve_cells dec_eq).
    move : c1nfclc => /orP [].
      by rewrite mem_cat => -> .
    rewrite !mem_cat => -> .
    by rewrite !orbT.
apply : contrapositive_close_imp_cont.
  apply: (allP srf _ c1open).
apply /andP; apply: (allP svalid _ c1open).
Qed.

Lemma lower_edge_new_cells e low_e high_e:
forall new_open_cells,
opening_cells (point e) (outgoing e) low_e high_e = new_open_cells ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
(low (head dummy_cell new_open_cells) == low_e).
Proof.
rewrite /opening_cells.
case : (sort (@edge_below R) (outgoing e)) => [/= |/= c q] newop.
  case valid : (vertical_intersection_point _ _) => [pl |//=].
    case valid2 : (vertical_intersection_point _ _) => [ph |//=].
      case : ifP.
        move => /eqP <-.
        case : ifP.
          by move => /eqP <- <- /=.
        by move => _ <- /=.
      by move => _<- /=.
    move => <- _ validh.
    move : valid2.
    by rewrite /vertical_intersection_point validh.
  move => <- validl.
  move : valid.
  by rewrite /vertical_intersection_point validl.
case valid : (vertical_intersection_point _ _) => [pl |//=].
  case : ifP.
    by move => /eqP <- <- /=.
  by move => _ <- /=.
move => _ validl _.
move : valid.
by rewrite /vertical_intersection_point validl.
Qed.

Definition out_left_event ev :=
  {in outgoing ev, forall e, left_pt e == point(ev)}.

Lemma open_not_nil out low_e high_e p :
valid_edge low_e p -> valid_edge high_e p ->
opening_cells_aux p out low_e high_e != [::].
Proof.
move => vlow vhigh.
case : out => [/= | ed out /=].

  case validl : (vertical_intersection_point p low_e) => [pl |  /= ]; first last.
    move : validl.
    by rewrite /vertical_intersection_point vlow.
  case validh : (vertical_intersection_point p high_e) => [ph |  /= ]; first last.
    move : validh.
    by rewrite /vertical_intersection_point vhigh.
  by [].
  case validl : (vertical_intersection_point p low_e) => [pl |  /= ]; first last.
  move : validl.
  by rewrite /vertical_intersection_point vlow.
case validh : (vertical_intersection_point p high_e) => [ph |  /= ]; first last.
  move : validh.
  by rewrite /vertical_intersection_point vhigh.
by [].
Qed.

Lemma opening_cells_not_nil out le he p :
  valid_edge le p -> valid_edge he p ->
  opening_cells p out le he != [::].
Proof.
move=> vle vhe; apply: (open_not_nil _ vle vhe).
(* Todo : report on strange error message if 
  apply: (open_not_nil vle vhe) is used instead. *)
Qed.

Lemma last_seq2 (T : Type) (def a : T) (s : seq T) :
   s <> nil -> last def (a :: s) = last def s.
Proof.
by case: s => [// | b s] _ /=.
Qed.

Lemma outleft_event_sort e :
  out_left_event e ->
  forall ed, ed \in sort (@edge_below R) (outgoing e) -> left_pt ed == point e.
Proof.
move=> outleft ed edin; apply: outleft.
by have <- := perm_mem (permEl (perm_sort (@edge_below _) (outgoing e))).
Qed.

Lemma higher_edge_new_cells e low_e high_e:
out_left_event e ->
forall new_open_cells,
opening_cells (point e) (outgoing e) low_e high_e =
   new_open_cells ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
(high (last dummy_cell new_open_cells) == high_e).
Proof.
rewrite /opening_cells.
move /outleft_event_sort.
elim : (sort (@edge_below R) (outgoing e)) low_e =>
  [/= | ed q IH ] low_e outleft openc.
  case h1 : (vertical_intersection_point (point e) low_e) => [pl |  /= ].
    case h2 : (vertical_intersection_point (point e) high_e) => [ph |  /= ].
      by move => <- .
    move => <- _ validh.
    move : h2.
    by rewrite /vertical_intersection_point validh.
  move => <-  validl .
  move : h1.
  by rewrite /vertical_intersection_point validl.
case valid : (vertical_intersection_point (point e) low_e) => [pl |  /= ]; first last.
  move =>  _ validl _.
  move :  valid.
  by rewrite /vertical_intersection_point validl.
case valid2 : (vertical_intersection_point (point e) high_e) => [ph |  /= ]; first last.
  move => <-   _ validh.
  move : valid2.
  by rewrite /vertical_intersection_point validh.
move => <- .
have : (valid_edge ed (point e)).
  apply valid_edge_extremities.
  by rewrite outleft // inE eqxx.
rewrite /=.
rewrite valid.
move : outleft.
move => /allP  /andP [/eqP lfteq /allP outleft].
move=> ved vlow vhigh.
rewrite last_seq2; last by apply/eqP/open_not_nil.
by apply: IH.
Qed.


Definition cells_low_e_top cells low_e : bool :=
  (cells != nil) && (low (head dummy_cell cells) == low_e) && (high (last dummy_cell cells) == top).

Definition cells_bottom_top cells : bool :=
  cells_low_e_top cells bottom.

Lemma bottom_imp_seq_below s p :
cells_bottom_top s -> inside_box p -> bottom_edge_seq_below s p.
Proof.
case s=> [// | c q].
rewrite /cells_bottom_top /cells_low_e_top => /andP []/andP [] _ /eqP /= loweq _.
rewrite /bottom_edge_seq_below  /inside_box loweq => /andP [] /andP []  /negP nsab _ _ /=.
by apply /underWC/negP.
Qed.


Lemma last_in_not_nil (A : eqType) (e : A) (s : seq A) :
s != [::] -> last e s \in s.
Proof.
case : s  => [//= | c q  ]  /= _.
by rewrite mem_last.
Qed.

Lemma head_in_not_nil (A : eqType) (e : A) (s : seq A) :
s != [::] -> head e s \in s.
Proof.
case : s  => [//= | c q  ]  /= _.
by rewrite inE eqxx.
Qed.

Lemma exists_cell_aux low_e p open :
cells_low_e_top open low_e -> adjacent_cells open ->
~ p <<< low_e ->  p <<< top ->
(exists c : cell, c \in open /\ contains_point p c).
Proof.
elim : open low_e => [//= | c0 q IH ].
case cont : (contains_point p c0).
  by exists c0; rewrite cont inE eqxx.
have := (IH (high c0)).
move => IH' low_e {IH}.
rewrite /cells_low_e_top => /andP[] /andP [] _ /= /eqP <- hightop.
move=> adj lowunder topabove.
  have : cells_low_e_top q (high c0).
  rewrite /cells_low_e_top /=.
  have qnnil: q!= nil.
    move : hightop lowunder topabove  cont {IH'} adj.
    case : q => //=.
    rewrite  /contains_point /=.
    by move => /eqP ->  /negP -> /underW ->.
  rewrite qnnil /=.
  move : hightop qnnil adj IH'.
  case : q => [ // | a q /=].
  move => hightop.
  by rewrite hightop eq_sym => _ /andP [] ->.
move => lowtop /=.

rewrite /contains_point in cont.
move : lowunder cont  => /negP /= -> /= /negbT phc0.
have phc := negP (underWC phc0  ).
have := (IH' lowtop (path_sorted adj) phc topabove) .
move => [] x [] xinq cpx.
exists x .
by rewrite in_cons xinq /= orbT cpx.
Qed.

Lemma exists_cell  p open :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
(exists c : cell, c \in open /\ contains_point p c).
Proof.
move=> cbtom adj inbox_e; apply:  (exists_cell_aux cbtom adj).
  move=>/underW abs.
  by move: inbox_e => /andP [] + _ => /andP[] /negP; rewrite abs.
by move: inbox_e => /andP[] + _ => /andP[].
Qed.

Definition cell_edges cells := map low cells ++ map high cells.

Lemma lhc_dec open p fc cc lc le he:
  cells_bottom_top open -> adjacent_cells open ->
  inside_box p ->
  open_cells_decomposition open p =  (fc, cc, lc, le, he) ->
  {lec & { hec & { cc' | 
       open = fc ++ cc ++ lc /\
       low lec = le /\ high hec = he /\ cc = lec :: cc' /\
       hec = last lec cc'}}}.
Proof.
move=> cbtom adj inbox_p oe.
have[/eqP <- [/eqP <- ]] :=
 l_h_c_decomposition oe (exists_cell cbtom adj inbox_p).
rewrite (decomposition_preserve_cells oe).
by case: cc {oe} => [// | lec cc']; exists lec, (last lec cc'), cc'.
Qed.

Lemma l_h_in_open (open : seq cell) p :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
exists lc hc, lc \in open /\ hc \in open /\ low lc =
   snd(fst (open_cells_decomposition open p)) /\
   high hc = snd (open_cells_decomposition open p).
Proof.
move=> cbtom adj inbox_p.
case oe : (open_cells_decomposition open p) => [[[[fc cc] lc] le] he].
move: (lhc_dec cbtom adj inbox_p oe) => [lec [hec [cc' [A [B [C [D E]]]]]]].
exists lec, hec.
split; first by rewrite A D /= !(mem_cat, inE) eqxx !orbT.
split; first by rewrite A D E !(mem_last, mem_cat, inE) !orbT.
split; first by rewrite B.
by rewrite C.
Qed.

Lemma close_out_from_event_sort event future :
  close_out_from_event event future ->
  all (end_edge^~ future) (sort (@edge_below R) (outgoing event)).
Proof.
move/allP=> outP; apply/allP=> x xin; apply outP.
by have <- := perm_mem (permEl (perm_sort (@edge_below R) (outgoing event))).
Qed.

Lemma opening_cells_close event low_e high_e future :
end_edge low_e future -> end_edge high_e future -> close_out_from_event event future ->
close_alive_edges (opening_cells (point event) (outgoing event) low_e high_e)
   future.
Proof.
rewrite /opening_cells.
move=> A B /close_out_from_event_sort; move: A B.
move : low_e high_e.
elim : (sort (@edge_below R) (outgoing event)) => [ | e0 q Ho].
  move => low_e high_e end_low end_high.
  move => close_events.
  rewrite /=.
  case : (vertical_intersection_point (point event) low_e) => [low_pt|]; last by [].
  case : (vertical_intersection_point (point event) high_e) => [high_pt|]; last by [].
  rewrite /=.
  by rewrite end_low end_high.
rewrite /=.
move => low_e high_e end_low end_high.
move => /andP [end0 close_future].
case : (vertical_intersection_point (point event) low_e) => [low_pt|]; last by [].
rewrite /=.
rewrite end_low end0 /=.
apply : Ho => //.
Qed.

Lemma head_not_end q e future_events :

close_alive_edges q (e :: future_events) ->
(forall c, (c \in q) ->
~ event_close_edge (low c) e /\ ~ event_close_edge (high c) e) ->
close_alive_edges q (future_events).
Proof.
elim q => [//| c' q' IH cae].
have cae': close_alive_edges q' (e :: future_events).
  move : cae.
  by rewrite /close_alive_edges /all => /andP [] /andP [] _ _.
move=> condition.
rewrite /=.
apply/andP; split; last first.
  apply: IH=> //.
  by move=> c cin; apply condition; rewrite inE cin orbT.
move: cae; rewrite /= /end_edge /= => /andP[] /andP[] /orP[].
  move=> -> C; rewrite orTb; move: C=> /orP[].
    by move=> ->.
  move=> /orP [abs | ].
  case: (condition c').
    by rewrite inE eqxx.
  by rewrite abs.
  by move=> ->; rewrite orbT.
  move=> /orP [abs | ].
  case: (condition c').
    by rewrite inE eqxx.
  by rewrite abs.
move=> ->; rewrite orbT.
move=> /orP[] .
    by move=> ->.
  move=> /orP [abs | ].
  case: (condition c').
    by rewrite inE eqxx.
  by rewrite abs.
by move=> ->; rewrite orbT.
Qed.

Lemma l_h_valid (open : seq cell) p :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
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

Lemma l_h_neq_contact open p high_e contact :
p <<= high_e ->
adjacent_cells open ->
seq_valid open p ->
s_right_form open ->
((p <<< high (last dummy_cell open)) && (high_e == low (head dummy_cell open)) && (open !=nil)) || ((open == nil) &&  (p <<< high_e)) ->
forall c_c last_c high_c, 
open_cells_decomposition_contact open p contact high_e = (c_c,last_c, high_c) ->
p <<< high_c.
Proof.
elim : open contact high_e  => [//= | c q Ih/=] contact high_e   /=.
 by rewrite andbF /= => _ _ _ _ pinfe a b c [] _ _ <-  .
rewrite orbF andbT.
move => pinfe  adjopen valopen rf_open pinfhighc c_c lc highc //.
case c_eq : c pinfhighc adjopen valopen rf_open => [lpts rpts lowc high_c].

case : ifP => [contain| notcontain {Ih}] /= pinfh adjopen valopen rf_open op_dec .
  
move : contain.
  rewrite /contains_point => /andP [] _ /= pinf_c.
  have := (Ih _ _  pinf_c _ _ _  _ _ _  _ op_dec )  =>  Ih' {Ih}.
  

  case : q adjopen  op_dec valopen rf_open pinfh Ih' => [//= |  c' q'  /= /andP [] -> -> op_dec] .
    rewrite andbF orFb /= => _ _ _ _ /andP [] -> _ a.
    by apply a.
  rewrite !andbT orbF =>  /andP [] _ /andP [] /andP [] -> -> -> /andP [] _ /andP [] -> -> /andP [] -> _ a.
  by apply a.

move : op_dec => [] _ _ <-. 
move : notcontain.
rewrite /contains_point /= .
move => /idPn.
rewrite negb_and => /orP [/negPn |].
  by move : pinfh => /andP  [] _ /eqP ->.
move : pinfh => /andP  [] _ /eqP heql .
rewrite heql in pinfe.
move : valopen => /andP [] /andP []  vallow valhigh _.
have vall': valid_edge (low c) p.
  by rewrite c_eq.
have valh': valid_edge (high c) p.
  by rewrite c_eq.
move : rf_open.
rewrite /= => /andP [] linfh _.
have inf' : low c <| high c.
  by rewrite c_eq.
have pinf : p <<= low c .
  by rewrite c_eq.
move => /negPf.
have := order_edges_viz_point vall' valh' inf' pinf.
by rewrite c_eq /= => -> .
Qed.

Lemma l_h_above_under_contact open p high_e contact :
p <<= high_e ->
forall c_c last_c high_c, 
open_cells_decomposition_contact open p contact high_e = (c_c,last_c, high_c) ->
p <<= high_c.
Proof.
elim : open contact high_e  => [//= | c open Ih] contact high_e pinf.
  by move => _ _ _ [] _ _ <-.
case : c=> [lpts rpts lowc highc].
rewrite /=.
case : ifP => [contain| notcontain]. 
  case h : (open_cells_decomposition_contact _ _ _ _) => [[cc lc]high_final].
  move => _ _ _ [] _ _ <-.
  have := Ih _ _ _ _ _ _ h => d.
  apply d.
  move : contain.
  by rewrite /contains_point /= => /andP [] _ pinfhc.
by move => _ _ _ [] _ _ <-.
Qed.

Lemma l_h_above_under_fix open_cells  p fc :
(exists c, (c \in open_cells) && contains_point p c)  ->
forall first_cells contact last_cells low_f high_f ,
open_cells_decomposition_fix open_cells p fc = (first_cells, contact, last_cells, low_f, high_f)   ->
~~( p <<< low_f) && (p <<= high_f).
Proof.
move => exi f_c c_c l_c lowf highf .
elim : open_cells fc exi => [//= fc []c' |c' q' IH /= fc].
  by [].
case : c' => [lpts rpts lowc highc] .
case : ifP => [contain |notcontain].
  case op_c: (open_cells_decomposition_contact _ _ _ _) => [/= []cc lc high_c] _ [] _ _ _ <- <-.
  move : contain.
  rewrite /contains_point /= => /andP [] -> pinfhc.
  by rewrite (l_h_above_under_contact pinfhc op_c) andbT.
move => [] c' /andP.

rewrite inE => [][] /orP [/eqP -> a|cin cont op_c].
  by rewrite a in notcontain.
apply : (IH _ _ op_c).
exists c'.
by rewrite cin cont.
Qed.

Lemma l_h_above_under open p :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
seq_valid open p ->
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition open p  =
  (first_cells, contact, last_cells, low_f, high_f) ->
~~ (p <<< low_f) /\ (p <<= high_f).
Proof.
case : open  => [//=| c q ] cbtop adjopen insbox opval fc cc lc lowf highf.
have := exists_cell cbtop adjopen insbox => [][]c' []cin cont.
have exi : (exists c0 : cell, (c0 \in c :: q) && contains_point p c0).
  exists c'.
  by rewrite cin cont.
rewrite /open_cells_decomposition => op_f. 
by have := (l_h_above_under_fix exi op_f) => /andP [].
Qed. 

Lemma l_h_above_under_strict open p :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
seq_valid open p ->
s_right_form open ->
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition open p  =
   (first_cells, contact, last_cells, low_f, high_f) ->
  p >>> low_f /\ p <<< high_f.
Proof.
move => cbtom adj inbox_p val rfo  fc cc lc le he oe.
have [lec [hec [cc' [ocd [leq [heq [ccq hecq]]]]]]]:=
      lhc_dec cbtom adj inbox_p oe.
have sb := bottom_imp_seq_below cbtom inbox_p.
have notc := decomposition_not_contain rfo val adj sb oe.
move: (inbox_p)=> /andP[] /andP[] pab plt _.
have [pale puhe] := l_h_above_under cbtom adj inbox_p val oe.
split.
  elim/last_ind: {2} (fc)  (erefl fc) => [ fceq | fc' lfc _ fceq].
    by move: cbtom; rewrite ocd fceq ccq -leq => /andP[] /andP[] _ /= /eqP ->.
  have lfco : lfc \in open by rewrite ocd fceq !(mem_cat, mem_rcons, inE) eqxx.
  move: adj; rewrite ocd ccq /= -adjacent_cut; last first.
    by rewrite fceq; case : (fc').
  rewrite fceq /= last_rcons -leq.
  move => /andP[] /andP[] /eqP /[dup] A <- _ _; apply/negP=> abs.
  have := notc lfc; rewrite fceq mem_rcons inE eqxx => /(_ isT).
  rewrite /contains_point abs andbT=> /negP; rewrite negbK => abs' {abs}.
  case/negP: pale.
  move: rfo => /allP /(_ lfc lfco) lbh.
  have [vall valh]:= andP (allP val lfc lfco).
  by rewrite -leq -A (order_edges_strict_viz_point vall valh).
case lceq : lc => [ | hlc lc'].
  move: cbtom; rewrite ocd lceq ccq cats0 -heq=> /andP[]/andP[] _ _.
  by rewrite last_cat /= -hecq => /eqP ->.
have hlco : hlc \in open by rewrite ocd lceq !(mem_cat, inE) eqxx !orbT.
move: adj; rewrite ocd catA lceq -adjacent_cut; last by rewrite ccq; case: (fc).
move=> /andP[] /andP[] + _ _; rewrite ccq last_cat /= -hecq heq.
move => /eqP /[dup] A ->.
rewrite -(negbK (_ <<< _)); apply/negP=> abs.
have := notc hlc; rewrite lceq inE eqxx orbT => /(_ isT).
rewrite /contains_point abs /=; apply => {abs}.
move: rfo => /allP /(_ hlc hlco) => lbh.
have [vall valh]:= andP (allP val hlc hlco).
by rewrite (order_edges_viz_point vall valh) // -A.
Qed.

Lemma higher_lower_equality e open :
out_left_event e ->
forall first_cells contact_cells last_cells low_e high_e,
open_cells_decomposition open (point e) =
(first_cells, contact_cells, last_cells, low_e, high_e) ->
forall new_cells,
(opening_cells (point e) (outgoing e) low_e high_e) =
  new_cells ->
(exists c : cell, c \in open /\ contains_point (point e) c) ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
low (head dummy_cell contact_cells) = low (head dummy_cell new_cells) /\
high (last dummy_cell contact_cells) = high (last dummy_cell new_cells) /\ contact_cells != nil.
Proof.
move => outleft fc c_c lc lowe highe op_c_d new_cells op_new exi lowv highv.
have := (lower_edge_new_cells op_new lowv highv) => /eqP low_new.
have := (higher_edge_new_cells outleft op_new lowv highv) => /eqP high_new.
have := (l_h_c_decomposition op_c_d  exi).
move => [] /eqP l_old [] /eqP h_old c_nnil.
by rewrite low_new high_new l_old h_old .
Qed.

Lemma opening_valid e low_e high_e:
out_left_event e ->
valid_edge low_e (point e) ->
valid_edge high_e (point e) ->
seq_valid (opening_cells (point e) (outgoing e) low_e high_e) (point e).
Proof.
rewrite /opening_cells.
move/outleft_event_sort.
move : low_e high_e.
elim out : (sort (@edge_below R) (outgoing e)) => [/= | c q IH] low_e high_e outl.
  rewrite /=.
  move => lowv highv.
  case : (vertical_intersection_point (point e) low_e) => [low_pt|]; last by [].
  case : (vertical_intersection_point (point e) high_e) => [high_pt|]; last by [].
  by rewrite /= lowv highv.
rewrite /=.
move => lowv highv.
case : (vertical_intersection_point (point e) low_e) => [low_pt|]; last by [].
rewrite /= lowv /=.
have cin : c \in c::q.
  by rewrite inE eqxx.
have leftp := (outl c cin).
  have valc: valid_edge c (point e).
  apply : valid_edge_extremities.
  by rewrite leftp.
rewrite valc /=.
have cond : (forall e0: edge_eqType R, e0 \in  q -> left_pt e0 == point e).
  move => e0 ein.
  apply : outl.
  by rewrite inE ein orbT.
apply (IH c high_e cond valc highv).
Qed.

Lemma valid_between_events g e p future :
lexPt e p ->
(forall e', e' \in future -> lexePt p (point e')) ->
valid_edge g e -> inside_box p -> end_edge g future ->
valid_edge g p.
Proof.
move => einfp pinffut vale.
rewrite /inside_box => /andP [] _ /andP [] botv topv.
rewrite /end_edge => /orP [].
  by rewrite !inE /valid_edge => /orP [] /eqP ->; rewrite !ltW;
  move: botv topv=> /andP[] a b /andP[] c d; rewrite ?(a,b,c,d).
move => /hasP [] e' e'in e'c.
have pinfe' := pinffut e' e'in.
rewrite /valid_edge; apply /andP; split.
  move : vale.
  rewrite /valid_edge => /andP [] ginfe _.
  move : einfp.
  rewrite /lexPt => /orP [esinfp | /andP [] /eqP <- //].
  by rewrite ltW // (le_lt_trans ginfe esinfp).
move : e'c.
rewrite /event_close_edge => /eqP ->.
move : pinfe'.
rewrite /lexPt => /orP [ | /andP [] /eqP -> //].
apply ltW .
Qed.

Lemma step_keeps_closeness open  e (future_events : seq event) :
inside_box (point e) ->
out_left_event e ->
s_right_form open ->
cells_bottom_top open ->
adjacent_cells open ->
seq_valid open (point e) ->
close_edges_from_events (e::future_events) ->
close_alive_edges open (e::future_events) ->
forall open2 closed closed2,
step e open closed = (open2, closed2) ->
close_alive_edges open2 future_events.
Proof.
move => insboxe outlefte srf cbtop adjop val_op_e close_ev close_ed  open2 closed closed2.
rewrite /step.
case op_dec : (open_cells_decomposition open (point e)) => [[[[fc cc] lc] low_e] high_e] /=.
move => [] <- _.
rewrite /opening_cells.
have beseqb := bottom_imp_seq_below cbtop insboxe.
have dec_not_end := decomposition_not_end srf val_op_e adjop beseqb op_dec.
have open_eq := decomposition_preserve_cells op_dec.
have := (l_h_valid cbtop adjop  insboxe val_op_e op_dec) => [][] lowv highv.
rewrite open_eq in val_op_e.
have exi := exists_cell cbtop adjop insboxe.
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top open_eq => /andP [] /andP [] _ /eqP openbottom /eqP opentop.
have := (open_not_nil (sort (@edge_below R) (outgoing e)) lowv highv).
case op_new : (opening_cells_aux (point e) _ low_e high_e)
   => [//=| cnew q'' /=] _.
have := higher_lower_equality outlefte op_dec op_new exi lowv highv .
rewrite /= => [][] low_eq [] high_eq ccnnil.
have lhc := l_h_c_decomposition op_dec exi .
case : cc op_dec open_eq val_op_e openbottom opentop low_eq high_eq ccnnil lhc => [//|c q  /=] op_dec open_eq val_op_e openbottom opentop low_eq high_eq ccnnil lhc.
have close_fc: close_alive_edges fc future_events.
  suff/head_not_end : close_alive_edges fc (e :: future_events).
    by apply=> c0 cin; apply: dec_not_end; rewrite cin.
  apply/allP=> c0 cin; apply (allP close_ed); rewrite open_eq.
  by rewrite mem_cat cin.
have close_lc: close_alive_edges lc future_events.
  suff/head_not_end : close_alive_edges lc (e :: future_events).
    by apply=> c0 cin; apply: dec_not_end; rewrite cin orbT.
  apply/allP=> c0 cin; apply (allP close_ed); rewrite open_eq.
  by rewrite mem_cat -cat_cons mem_cat cin !orbT.
have endlowe: end_edge low_e future_events.
  case : fc op_dec open_eq val_op_e openbottom opentop close_fc dec_not_end lhc  => [/=|c' q' ] op_dec open_eq val_op_e openbottom opentop close_fc dec_not_end .
    rewrite /end_edge !inE openbottom => [][] /eqP <- _.
    by rewrite eqxx.
  move => [] /eqP <- _.
  move : adjop.
  rewrite open_eq -adjacent_cut //.
  rewrite low_eq.
  move => /andP [] /andP [] /eqP <- _ _.
  rewrite /=.
  by move: (allP close_fc (last c' q'))  => /(_  (mem_last _ _))/andP[].
have endhighe: end_edge high_e future_events.
  case : lc op_dec open_eq val_op_e openbottom opentop close_lc dec_not_end lhc => [/=|c' q' ] op_dec open_eq val_op_e openbottom opentop close_lc dec_not_end []/eqP low_eq2 [] /eqP high_eq2 _.
    rewrite last_cat /= last_cat /= in opentop.
    by rewrite -high_eq2 /end_edge !inE opentop eqxx ?orbT .
  rewrite -high_eq2.
  move : adjop.
  rewrite open_eq (catA fc (c :: q) (c' :: q')) -(adjacent_cut c'); first last.
  by case : (fc).  
 
  rewrite  last_cat /= => /andP []/andP [] /eqP -> _ _.
    have cin : c' \in c'::q'.
    by rewrite inE eqxx.
  by move: (allP close_lc (c') cin) => /andP [].
move : close_ev.
rewrite /= => /andP [] cle _.
have close_new:= opening_cells_close endlowe endhighe cle.
rewrite /opening_cells op_new in close_new.
apply (insert_opening_closeness close_fc close_new close_lc).
Qed.

Lemma step_keeps_valid (open : seq cell) (e : event) (p : pt) (future_events : seq event) :
inside_box p ->
inside_box (point e) ->
lexPt (point e) p ->
out_left_event e ->
s_right_form open ->
cells_bottom_top open ->
adjacent_cells open ->
seq_valid open (point e) ->
close_alive_edges open (e::future_events) ->
close_edges_from_events (e::future_events) ->
(forall e', e' \in future_events -> lexePt p (point e')) ->
forall open2 closed closed2,
step e open closed = (open2, closed2) ->
seq_valid open2 p.
Proof.
move => insboxp insboxe einfp outlefte srf cbtop adjop val_op_e close_ed close_ev pinfe' open2 closed closed2 step.
have close_all := step_keeps_closeness insboxe outlefte srf cbtop adjop val_op_e close_ev close_ed step.
move : step.
rewrite /step.
case op_dec : (open_cells_decomposition open (point e)) => [[[[fc cc] lc] low_e] high_e] /=.
have exi := exists_cell cbtop adjop insboxe.
have lhc := l_h_c_decomposition op_dec exi .
rewrite /opening_cells => -[] open2eq _.
rewrite -open2eq in close_all.
rewrite -open2eq{open2eq}.
have beseqb := bottom_imp_seq_below cbtop insboxe.
have dec_not_end := decomposition_not_end srf val_op_e adjop beseqb op_dec.
have open_eq := decomposition_preserve_cells op_dec.

have := (l_h_valid cbtop adjop  insboxe val_op_e op_dec) => [][] lowv highv.
rewrite open_eq in val_op_e.
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top open_eq => /andP [] /andP [] _ /eqP openbottom /eqP opentop.
have := (open_not_nil (sort (@edge_below R) (outgoing e)) lowv highv).
case op_new : (opening_cells_aux (point e) _ low_e high_e)
   => [//= | cnew q'' /=] _.
have := higher_lower_equality outlefte op_dec op_new exi lowv highv .
rewrite /= => [][] low_eq [] high_eq ccnnil.

case : cc op_dec open_eq val_op_e openbottom opentop low_eq high_eq ccnnil lhc => [//|c q  /=] op_dec open_eq val_op_e openbottom opentop low_eq high_eq ccnnil lhc.
have := opening_valid outlefte lowv highv; rewrite /opening_cells.
rewrite op_new => valnew.
rewrite /seq_valid  all_cat -cat_cons all_cat in val_op_e.
move : val_op_e => /andP [] valfc  /andP [] _ vallc.
have valall := insert_opening_all valfc valnew vallc.
rewrite /seq_valid.
apply /allP .
move => c' cin.
move : close_all.
rewrite /close_alive_edges op_new => /allP.
move => end_all.
have := end_all c' cin => /andP [] endlowc' endhighc'.
have : valid_edge (low c') (point e) && valid_edge (high c') (point e).
  move : valall => /allP valall.
  apply (valall c' cin).
move => /andP [] vlowc'e vhighc'e.
by rewrite(valid_between_events einfp pinfe' vlowc'e insboxp endlowc')( valid_between_events einfp pinfe' vhighc'e insboxp endhighc') .
Qed.

(* toutes les arêtes présentes dans la liste des événements qui sont déjà vivantes sont dans la liste des cellules
   car dans un second temps la liste des cellules qu'on obtient à la fin doit contenir toutes les arêtes
   après un certain événement
   il faut vérifier que on ouvre pour une certaine hauteur tout ce qu'on ferme.

*)

Lemma adjacent_opening_aux' p s le he new :
  opening_cells_aux p s le he = new -> 
  adjacent_cells new /\ (new != nil -> low (head dummy_cell new) = le).
Proof.
elim: s le new => [ | g s Ih] le new /=; set vip := vertical_intersection_point.
  case vip1 : (vip R p le) => [p1 | ]; last by move=> <-.
  case vip2 : (vip R p he) => [p2 | ]; last by move=> <-.
  by case: ifP => _ <- //=.
case: (vip R p le) => [p1 | ]; last by move=> <-.
by case: ifP => testres <- //=;
  (split; last by [];
  move: (Ih g _ erefl) => []; case: (opening_cells_aux _ _ _ _) => //=;
  move=> a l -> ->; rewrite // eqxx).
Qed.

Lemma adjacent_opening' p s le he:
  adjacent_cells (opening_cells_aux p s le he).
Proof.
case: s => [| g s ] /=; set vip := vertical_intersection_point.
  case vip1 : (vip R p le) => [p1 | ]; last by [].
  by case vip2 : (vip R p he) => [p2 | ].
case: (vip R p le) => [p1 | ]; last by [].
rewrite /=.
move: (@adjacent_opening_aux' p s g he _ erefl).
case: (opening_cells_aux _ _ _ _) => //=.
by move=> a l [] -> ->; rewrite // eqxx.
Qed.
  
(*
Lemma replacing_seq_adjacent_aux c l1 l2 fc lc :
l1 != nil -> l2 != nil ->
low (head dummy_cell l1) = low (head dummy_cell l2) ->
high (last dummy_cell l1) = high (last dummy_cell l2) ->
adjacent_cells_aux  (fc ++ l1 ++ lc) (high c)->
adjacent_cells_aux l2 (high (last c fc)) ->
adjacent_cells_aux (fc ++ l2 ++ lc) (high c).
Proof.
case : l1 => [//= | c1 q1 _].
case : l2 => [//= | c2 q2 _].
rewrite !adj_aux_path.
rewrite !cat_path.
move => /= Hlow Hhigh.
move => /andP [] -> /=.
rewrite Hlow => /andP [] /andP [] -> /= pathq1 pathlc -> /=.

case : lc pathlc => [//= | cl ql /= ].
by rewrite Hhigh.
Qed.
*)

Lemma replacing_seq_adjacent l1 l2 fc lc :
l1 != nil -> l2 != nil ->
low (head dummy_cell l1) = low (head dummy_cell l2) ->
high (last dummy_cell l1) = high (last dummy_cell l2) ->
adjacent_cells (fc ++ l1 ++ lc) ->
adjacent_cells l2 ->
adjacent_cells (fc ++ l2 ++ lc).
Proof.
rewrite /adjacent_cells; case: fc => [ | a0 fc] /=; case: l1 => //=;
   case: l2 => //=; move=> a2 l2 a1 l1 _ _ a1a2 l1l2.
  rewrite cat_path => /andP[] pl1 plc pl2; rewrite cat_path pl2.
  by move: plc; case: lc => [// | a3 l3 /=]; rewrite -l1l2.
rewrite cat_path /= cat_path => /andP[] pfc /andP[] jfca1 /andP[] pl1 plc pl2.
rewrite cat_path /= cat_path; rewrite pfc -a1a2 jfca1 pl2.
by move: plc; case: lc => [// | a3 l3 /=]; rewrite -l1l2.
Qed.

Lemma step_keeps_adjacent open  e  :
inside_box (point e) ->
out_left_event e ->
seq_valid open (point e) ->
cells_bottom_top open ->
forall closed open2 closed2,
 step e open closed = (open2, closed2) ->
adjacent_cells open -> adjacent_cells open2.
Proof.
rewrite /step .
move => insbox outleft  validopen cbtop closed open2 closed2.
move: (outleft) => /outleft_event_sort outleft'.
case op_c_d : (open_cells_decomposition open (point e)) =>  [[[[first_cells contact_cells] last_cells ]low_e] high_e].
rewrite /opening_cells.
move => [] <- _ adjopen.
have exi := (exists_cell cbtop adjopen insbox ).
have openeq := decomposition_preserve_cells op_c_d.
have := (l_h_valid cbtop adjopen  insbox validopen op_c_d).
move => [] lowv highv.
have := (open_not_nil (sort (@edge_below R) (outgoing e)) lowv highv).
case op_new : (opening_cells_aux (point e) _ low_e high_e)
  => [//= | q l ] qlnnil.
have := higher_lower_equality outleft op_c_d op_new exi lowv highv => [][] l_eq [] h_eq c_nnil.
have adjnew : adjacent_cells (q :: l).
  by rewrite -op_new; apply:adjacent_opening'.
rewrite openeq in adjopen.
apply : (replacing_seq_adjacent c_nnil qlnnil l_eq h_eq adjopen adjnew).
Qed.


Lemma middle_seq_not_nil  (A : eqType) (a b c : seq A) :
b != [::] ->
a ++ b ++ c != [::].
Proof.
rewrite -size_eq0 => /negP sizebneq0 /=.
apply  /negP.
rewrite -size_eq0 !size_cat /= !addn_eq0 .
apply  /negP /andP => [] /andP .
move => /andP [] _ /andP [] sizebeq0.
by rewrite sizebeq0 in sizebneq0.
Qed.

Lemma step_keeps_bottom open e  :
inside_box (point e) ->
seq_valid open (point e) ->
adjacent_cells open ->
cells_bottom_top open ->
forall closed open2 closed2,
step e open closed = (open2, closed2) ->
(open2 != nil) && (low (head dummy_cell open2) == bottom).
Proof.
move => insbox openvalid adjopen cbtop closed open2 closed2 .
rewrite /step /=.
case op_c_d : (open_cells_decomposition open (point e)) =>  [[[[first_cells contact_cells] last_cells ]low_e] high_e].
have op_dec := (decomposition_preserve_cells op_c_d).
rewrite /opening_cells.
move => [] <- _.
have := (l_h_valid cbtop adjopen insbox openvalid op_c_d).
move => [] lowv highv.
have exi := (exists_cell cbtop adjopen insbox ).
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top => /andP [] /andP [] opnnil /eqP openbottom /eqP _.
have newnnil := open_not_nil (sort (@edge_below R) (outgoing e)) lowv highv.
have newopnnil := (middle_seq_not_nil first_cells last_cells newnnil).
rewrite newopnnil /=.
case op_new : (opening_cells_aux (point e) _ low_e high_e) => [// | c q].
  by rewrite op_new in newnnil.
have := (lower_edge_new_cells op_new lowv highv) => /eqP /= low_new.
have := (l_h_c_decomposition op_c_d  exi).
move => [] /eqP l_old [] /eqP _ c_nnil.
rewrite -low_new in l_old.
case : first_cells op_c_d op_dec newopnnil => [/= |c1 q1 /=] op_c_d op_dec newopnnil.
  rewrite -l_old -openbottom op_dec /= .
  by case c_c : contact_cells c_nnil l_old op_c_d op_dec => [// | c' q' /=] _  -> .
by rewrite -openbottom op_dec /=.
Qed.

Lemma step_keeps_bottom_top open e  :
inside_box (point e) ->
seq_valid open (point e) ->
adjacent_cells open ->
cells_bottom_top open ->
out_left_event e ->
forall closed open2 closed2,
 step e open closed = (open2, closed2) ->
cells_bottom_top open2.
Proof.
move => insbox openvalid adjopen cbtop outleft closed open2 closed2 step .
rewrite /cells_bottom_top /cells_low_e_top.
rewrite (step_keeps_bottom insbox openvalid adjopen cbtop step) /=.
move : step.
rewrite /step /=.
case op_c_d : (open_cells_decomposition open (point e)) =>  [[[[first_cells contact_cells] last_cells ]low_e] high_e].
rewrite /opening_cells.
have op_dec := (decomposition_preserve_cells op_c_d).
move => [] <- _.
have := (l_h_valid cbtop adjopen insbox openvalid op_c_d).
move => [] lowv highv.
have exi := (exists_cell cbtop adjopen insbox ).
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top => /andP [] /andP [] opnnil /eqP _ /eqP opentop.
have newnnil := open_not_nil (sort (@edge_below R) (outgoing e)) lowv highv.
have newopnnil := (middle_seq_not_nil first_cells last_cells newnnil).
case op_new : (opening_cells_aux (point e) _ low_e high_e) => [// | c q].
  by rewrite op_new in newnnil.
have := higher_lower_equality outleft op_c_d op_new exi lowv highv => [][] _ [] /= h_eq c_nnil.
case : last_cells op_c_d op_dec newopnnil => [/= op_c_d |c1 q1 _ op_dec /=]  .
  rewrite !cats0 -opentop last_cat  => -> newn_nil /=.
  rewrite last_cat -h_eq.
  by case  : contact_cells c_nnil h_eq op_c_d.
by rewrite -opentop op_dec !last_cat /= last_cat.
Qed.

Definition no_crossing'  : Prop:=
 forall e e' : edge,
 valid_edge e (left_pt e') ->
(left_pt e' <<< e  -> e' <| e)  /\
(~ (left_pt e' <<= e)  -> e <| e').

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
  case lp: (vertical_intersection_point (point e) low_e) => [low_p /= |//].
  have := intersection_on_edge lp=> [][] poel lx_eq.
  case hp: (vertical_intersection_point (point e) high_e) => [high_p /= |//].
  have := intersection_on_edge hp=> [][] poeh hx_eq.
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
  move => e1 e2 e1in e2in .
  apply nc.
    by rewrite inE e1in orbT.
  by rewrite inE e2in orbT.
  case lp: (vertical_intersection_point (point e) low_e) => [low_p /= |//].
have := intersection_on_edge lp=> [][] poel lx_eq.

case : ifP=> [/eqP <-/=|/= _].
  rewrite inE => /orP  [/eqP -> /=|].
    by rewrite lexePt_refl.
  apply (IH c' einfc' c'v outq nc' c'infh).
rewrite inE => /orP  [/eqP -> /=|].
  have : p_y low_p <= p_y (point e).
    by rewrite leNgt -(strict_under_edge_lower_y lx_eq poel).
  rewrite /lexePt lx_eq eqxx=> ->.
  by rewrite orbT.
apply : (IH c' einfc' c'v outq nc' c'infh).
Qed.

Lemma open_cells_decomposition_low_under_high open p fc cc lc le he:
  {in [seq low c | c <- open] ++ [seq high c | c <- open] &, no_crossing R} ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  seq_valid open p ->
  s_right_form open ->
  open_cells_decomposition open p = (fc, cc, lc, le, he) ->
  le <| he.
Proof.
move=> n_c cbtom adj insp valp r_f op_c_d_eq.
have [lc' [hc' [lcin [hcin]]]] := l_h_in_open cbtom adj insp.
  rewrite op_c_d_eq //=  => [][le_eq he_eq].
have lein : le \in [seq low c | c <- open] ++ [seq high c | c <- open].
  by rewrite mem_cat; apply/orP; left; apply/mapP; exists lc'.
have hein : he \in [seq low c | c <- open] ++ [seq high c | c <- open].
  by rewrite mem_cat; apply/orP; right; apply/mapP; exists hc'.
have [// | abs_he_under_le ] :=  n_c le he lein hein.
have [e1 e2]:= l_h_above_under_strict cbtom adj insp valp r_f op_c_d_eq.
case/negP: e1.
have [vl vh]  : valid_edge le p /\ valid_edge he p.
  by split; move: valp =>/[dup]/allP/(_ _ lcin)/andP[] + +
             /allP/(_ _ hcin)/andP[]; rewrite le_eq he_eq.
by have /underW := (order_edges_strict_viz_point' vh vl abs_he_under_le e2).
Qed.

Definition events_to_edges := flatten \o (map outgoing).

Definition all_edges cells events :=
  cell_edges cells ++ events_to_edges events.

Lemma step_keeps_left_pts_inf e (future_events : seq event) p old_open : 
inside_box (point e) -> out_left_event e ->
s_right_form old_open -> seq_valid old_open (point e) ->
adjacent_cells old_open -> cells_bottom_top old_open ->
close_alive_edges old_open (e :: future_events) ->
close_edges_from_events (e :: future_events) ->
{in  all_edges old_open (e :: future_events) &, no_crossing R} ->
(forall c, c \in old_open ->
   p_x (last dummy_pt (left_pts c)) <= p_x (point e)) ->
forall new_open new_closed closed,
step e old_open closed  = (new_open, new_closed) ->
(lexPt (point e) p) ->
forall c, c \in new_open -> p_x (last dummy_pt (left_pts c)) <= p_x p.
Proof.
move => insboxe outlefte srf openval adjopen cbtom close_ed close_ev  n_c old_keep_left new_open new_closed closed step einfp.
move => c cin .
have cbtop_new := step_keeps_bottom_top insboxe openval adjopen cbtom outlefte step.
have adj_new := step_keeps_adjacent insboxe outlefte openval cbtom step adjopen.
move : step.
rewrite /step.
case op_c_d : (open_cells_decomposition old_open (point e)) =>  [[[[first_cells contact_cells] last_cells ]low_e] high_e].
have op_dec := (decomposition_preserve_cells op_c_d).
move => [] new_eq _.
move : cin.
rewrite op_dec in old_keep_left.
rewrite -new_eq !mem_cat orbCA => /orP [| /orP [cin | cin]]; first last.
    move/lexPtW/lexePt_xW: einfp.
    suff : p_x (last dummy_pt (left_pts c)) <= p_x (point e) by apply: le_trans.
    have := old_keep_left c.
    by rewrite !mem_cat cin !orbT /= => /(_ isT).
  move/lexPtW/lexePt_xW: einfp.
  suff : p_x (last dummy_pt (left_pts c)) <= p_x (point e) by apply: le_trans.
  have := old_keep_left c.
  by rewrite mem_cat cin  /= => /(_ isT).
move => cin. 
have [lowinfe einfhigh] :=
   l_h_above_under_strict cbtom adjopen insboxe openval srf op_c_d.
have [vallow valhigh]:= l_h_valid cbtom adjopen insboxe openval op_c_d.
have linfh : low_e <| high_e.
  have n_c' : {in [seq low i | i <- old_open] ++ [seq high i | i <- old_open] &,
                 no_crossing R}.
    have sub_cat (s1 s2 : seq edge): forall x, x \in s1 -> x \in s1 ++ s2.
      by move=> x; rewrite mem_cat => ->.
    by move: n_c; rewrite /all_edges /cell_edges=> /(sub_in2 (sub_cat _ _)).
  by apply: open_cells_decomposition_low_under_high _ _ _ _ _ op_c_d.
have n_c' : {in rcons (low_e :: sort (@edge_below R) (outgoing e)) high_e &, no_crossing R}.
  have [lc1 [lc2 [lc1in [lc2in]]]] := l_h_in_open cbtom adjopen insboxe.
    rewrite op_c_d /= => [][lowlc1 highlc2].
  have subseq:
    forall x, x \in rcons (low_e :: sort (@edge_below R) (outgoing e)) high_e ->
          x \in all_edges old_open (e :: future_events).
    move=> x; rewrite -cats1 mem_cat 2!inE 2!mem_cat orbAC=> /orP[].
      by move=>/orP[]/eqP ->; rewrite -?lowlc1 -?highlc2 map_f ?orbT.
    rewrite mem_sort=> xin; apply/orP; right.
    by apply/flattenP; exists (outgoing e); rewrite // inE eqxx.
  by apply: (sub_in2 subseq).
have lowinfe' : ~~ (point e <<< low_e).
  move : lowinfe => lowinfe.
  apply (underWC lowinfe).
have cinfe := (opening_cells_last_lexePt outlefte lowinfe' einfhigh vallow valhigh n_c' linfh cin).
by apply/(le_trans (lexePt_xW cinfe))/lexePt_xW/lexPtW.
Qed.

Lemma step_keeps_right_form e open closed op2 cl2 :
  cells_bottom_top open -> adjacent_cells open -> 
  inside_box (point e) -> seq_valid open (point e) ->
  {in ([seq low c | c <- open] ++ [seq high c | c <- open]) ++
      outgoing e &, no_crossing R} ->
  out_left_event e ->
  s_right_form open ->
  step e open closed = (op2, cl2) ->
  s_right_form op2.
Proof.
move=> cbtom adj inbox_e sval noc oute rfo; rewrite /step /=.
case oe : (open_cells_decomposition open (point e)) => [[[[fc cc] lc] le] he].
move=> [] <- _.
have [c1 [c2 [cc' [ocd [le_eq [he_eq [cceq lceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
have c1in : c1 \in open by rewrite ocd cceq !(mem_cat, inE, eqxx, orbT).
have c2in : c2 \in open.
  by rewrite ocd cceq !mem_cat lceq mem_last !orbT.
have [lP hP] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
set bigs := cell_edges open ++ outgoing e.
have lein : le \in bigs by rewrite -le_eq !mem_cat map_f.
have hein : he \in bigs by rewrite -he_eq !mem_cat map_f ?orbT.
have obig : {subset outgoing e <= bigs}.
  by move=> g gin; rewrite !mem_cat gin orbT.
have lev : valid_edge le (point e) by have [] := l_h_valid _ _ _ _ oe.
have hev : valid_edge he (point e) by have [] := l_h_valid _ _ _ _ oe.
have [edgesabove edgesbelow nocout] :=
   outgoing_conditions lP hP lein hein lev hev obig noc oute.
have /allP rfn : s_right_form 
    (opening_cells (point e) (outgoing e) le he).
  apply: (opening_cells_right_form hev (underWC lP) hP _ oute) => //.
  apply: (edge_below_from_point_under _ _ _ (underW hP) lP) => //.
  by apply: noc; rewrite -?le_eq -?he_eq !mem_cat map_f ?orbT.
apply/allP=> x; rewrite !mem_cat orbCA=> /orP[/rfn// | ].
by move=> xin; apply: (allP rfo); rewrite ocd !mem_cat orbCA xin orbT.
Qed.

Lemma size_open_ok (p : pt) (out : seq edge) (low_e : edge) (high_e : edge) :
valid_edge low_e p ->
valid_edge high_e p ->
(forall e, e \in out -> left_pt e == p) ->
let open :=  opening_cells_aux p out low_e high_e in
(size open = size out + 1)%N.
Proof.
elim :out low_e =>[ /=|op0 op1 Ih /=] low_e vl vh cond_out.
  have [lp ->] := (exists_point_valid vl).
  by have [hp -> /=] := (exists_point_valid vh).
have [lp -> /=] := (exists_point_valid vl).
rewrite addSn; congr (_.+1); apply: Ih=> //; last first.
  by move=> e ein; apply: cond_out; rewrite inE ein orbT.
by apply: valid_edge_extremities; rewrite cond_out // inE eqxx.
Qed.

Lemma mono_cell_edges s1 s2 : {subset s1 <= s2} ->
  {subset cell_edges s1 <= cell_edges s2}.
Proof.
by move=> sub g; rewrite mem_cat => /orP[] /mapP[c cin geq];
  rewrite /cell_edges geq mem_cat map_f ?orbT // sub.
Qed.

Lemma cell_edges_catC s1 s2 :
  cell_edges (s1 ++ s2) =i cell_edges (s2 ++ s1).
Proof.
move=> g.
by apply/idP/idP; apply: mono_cell_edges => {}g; rewrite !mem_cat orbC.
Qed.

Lemma cell_edges_cat (s1 s2 : seq cell) :
  cell_edges (s1 ++ s2) =i cell_edges s1 ++ cell_edges s2.
Proof.
move=> g; rewrite /cell_edges !(mem_cat, map_cat) !orbA; congr (_ || _).
by rewrite -!orbA; congr (_ || _); rewrite orbC.
Qed.

Lemma cell_edges_catCA s1 s2 s3 :
  cell_edges (s1 ++ s2 ++ s3) =i cell_edges (s2 ++ s1 ++ s3).
Proof.
move=> g; rewrite 2!catA [in LHS]cell_edges_cat [in RHS]cell_edges_cat.
rewrite [in LHS]mem_cat [in RHS]mem_cat; congr (_ || _).
by rewrite cell_edges_catC.
Qed.

Lemma cell_edges_opening_cells p s le he :
  {subset cell_edges (opening_cells p s le he) <= s ++ [:: le; he]}.
Proof.
by move=> g; rewrite mem_cat=>/orP[] /mapP[c cin ->];
  have := opening_cells_subset cin => /andP[]; rewrite !(mem_cat, inE) =>
    /orP[A | B] /orP[C | D]; rewrite ?A ?B ?C ?D ?orbT.
Qed.

(* This will be necessary to prove that the no_crossing property is preserved. *)
Lemma step_edges_open_subset e open closed open' closed' :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  step e open closed = (open', closed') ->
  {subset cell_edges open' <= cell_edges open ++ outgoing e}.
Proof.
move=> cbtom adj inbox_e; rewrite /step /=.
case oe: (open_cells_decomposition open (point e)) => [[[[fc cc] lc] le] he] [].
have dcp := decomposition_preserve_cells oe.
have new : {subset cell_edges
   (opening_cells (point e) (outgoing e) le he) <=
      cell_edges open ++ outgoing e}.
  move=> g /cell_edges_opening_cells; rewrite !mem_cat=>/orP[-> | loh].
    by rewrite orbT.
  have [cle [che [clein [chein]]]] := l_h_in_open cbtom adj inbox_e.
  move: loh => /[swap]; rewrite oe /= !inE => -[<- <-] /orP[]/eqP ->.
    by apply/orP; left; apply/orP; left; apply/mapP; exists cle.
  by apply/orP; left; apply/orP; right; apply/mapP; exists che.
move=> <- _ x.
rewrite !cell_edges_cat mem_cat !cell_edges_cat [X in _ || X]mem_cat.
rewrite orbCA=> /orP[ | fclc ]; first by apply: new.
rewrite dcp mem_cat cell_edges_catCA. 
by rewrite cell_edges_cat mem_cat cell_edges_cat [X in _ || X || _]mem_cat fclc orbT.
Qed.

Definition cover_left_of p s1 s2 :=
  forall q, inside_box q -> lexePt q p ->
  has (inside_open_cell q) s1 || has (inside_closed_cell q) s2.

(* TODO : rename, as there is no use of the lexicographic order
  anymore. *)
Definition bottom_left_cells_lex (open : seq cell) p :=
  forall c, c \in open -> p_x (last dummy_pt (left_pts c)) <= p_x p.

Lemma no_dup_seq_x3 e2 a b c:
  vertical_intersection_point a e2 = Some c ->
  p_x (last dummy_pt (no_dup_seq [:: b; a; c])) = p_x a.
Proof.
move => /intersection_on_edge [_ cq]; rewrite /=.
by repeat (case: ifP=> _ /=).
Qed.

Lemma contains_to_inside_open_cell open evs c p :
  seq_valid open p -> close_alive_edges open evs ->
  inside_box p ->
  p_x (last dummy_pt (left_pts c)) <= p_x p ->
  all (lexePt p) [seq point e | e <- evs] ->
  c \in open -> contains_point p c -> inside_open_cell p c.
Proof.
rewrite /inside_open_cell=> val clae inbox_p leftb rightb cin ->. 
rewrite leftb.
have cledge g : end_edge g evs -> p_x p <= p_x (right_pt g).
  have [/ltW pbot /ltW ptop] : p_x p < p_x (right_pt bottom) /\
             p_x p < p_x (right_pt top).
    by apply/andP; move:inbox_p=> /andP[] _ /andP[] /andP[] _ -> /andP[] _ ->.
  move=>/orP[]; [by rewrite !inE => /orP[]/eqP -> | ].
  move/hasP=> [ev' ev'in /eqP ->].
  apply: lexePt_xW.
  by apply/(allP rightb)/map_f.
have /andP [cmp1 cmp2] : (p_x p <= p_x (right_pt (low c))) &&
                (p_x p <= p_x (right_pt (high c))).
  by apply/andP; split; apply/cledge; move/allP: clae=> /(_ _ cin)/andP[].
rewrite /open_limit.
by case: (ltrP (p_x (right_pt (low c))) (p_x (right_pt (high c))))=> //.
Qed.

Lemma open_cells_decomposition_contains open p fc cc lc le he c:
  open_cells_decomposition open p = (fc, cc, lc, le, he) ->
  c \in cc -> contains_point p c.
Proof.
have contactP : forall s ct lc hh bcc g, 
  open_cells_decomposition_contact s p bcc g = (ct, lc, hh) ->
  {in bcc, forall c, contains_point p c} ->
  {in ct, forall c, contains_point p c}.
  move=> {lc}.
  elim=> [ | [l1 l2 g1 g2] s Ih] ct lc hh bcc g /=; first by move=> [] -> //.
  case: ifP=> ctn ocd_eq bcc_ctn.
    have acc_ctn:
     {in rcons bcc (Bcell l1 l2 g1 g2), forall c, contains_point p c}.
      move=> x; rewrite -cats1 mem_cat inE=> /orP[]; first by apply: bcc_ctn.
      by move/eqP=> ->.
    by have:= Ih _ _ _ _ _ ocd_eq acc_ctn.
  by move: ocd_eq=> [] <-.
rewrite /open_cells_decomposition; case: open; first by move=> [] _ <-.
move=> a l.
move: nil; elim: {a l}(a :: l) => /=; first by move=> acc [] _ <-.
move=> [lefts rights le' he'] s Ih acc.
case: ifP=> ctn; last by apply: Ih.
move=>{Ih}.
case ct_eq : (open_cells_decomposition_contact s p [::] he') => [[ct lst] g].
have Pnil : {in [::], forall c, contains_point p c} by move=> * *.
move/contactP: (ct_eq)=> /(_ Pnil) ctn'.
move=> [] _ <- _ _ _; rewrite inE => /orP[/eqP -> //| ].
by apply: ctn'.
Qed.

Lemma close_cell_equivalence_head p c:
  p === high c -> close_cell HEAD p c = close_cell SINGLE p c.
Proof.
move=> on.
rewrite /close_cell /build_right_pts.
case vip1 : (vertical_intersection_point _ _) => [p1 | //].
case vip2 : (vertical_intersection_point _ _) => [p2 | //].
have := intersection_on_edge vip2=> -[on2 xs].
have /eqP pp2 : p == p2 by rewrite pt_eqE (on_edge_same_point on on2) xs eqxx.
by rewrite /= pp2 eqxx.
Qed.

Lemma close_cell_equivalence_last p c:
  p === low c -> close_cell LAST p c = close_cell SINGLE p c.
Proof.
move=> on.
rewrite /close_cell /build_right_pts.
case vip1 : (vertical_intersection_point _ _) => [p1 | //].
case vip2 : (vertical_intersection_point _ _) => [p2 | //].
have := intersection_on_edge vip1=> -[on1 xs].
have /eqP pp1 : p == p1 by rewrite pt_eqE (on_edge_same_point on on1) xs eqxx.
by rewrite /= pp1 eqxx.
Qed.

Lemma close_cell_equivalence_middle p c:
  p === low c -> p === high c -> close_cell MIDDLE p c = close_cell SINGLE p c.
Proof.
move=> onl onh.
rewrite /close_cell /build_right_pts.
case vip1 : (vertical_intersection_point _ _) => [p1 | //].
case vip2 : (vertical_intersection_point _ _) => [p2 | //].
have := intersection_on_edge vip1=> -[on1 x1].
have := intersection_on_edge vip2=> -[on2 x2].
have /eqP pp1 : p == p1 by rewrite pt_eqE (on_edge_same_point onl on1) x1 eqxx.
have /eqP pp2 : p == p2 by rewrite pt_eqE (on_edge_same_point onh on2) x2 eqxx.
by rewrite /= -pp1 -pp2 eqxx.
Qed.

Lemma behead_cutlasteq (T : Type) a (s : seq T) :
  (1 < size s)%N -> s = head a s :: rcons (cutlast (behead s)) (last a s).
Proof.
by case: s => [ | b [ | c s]] //= _; congr (_ :: _); rewrite -lastI.
Qed.

Lemma cutlast_subset (T : eqType) (s : seq T) : {subset cutlast s <= s}.
Proof.
rewrite /cutlast; case: s => [// | a s].
elim: s a => [ // | b s Ih /=] a e; rewrite inE=> /orP[/eqP -> | ein].
  by rewrite inE eqxx.
by rewrite inE Ih ?orbT.
Qed.

Lemma behead_subset (T : eqType) (s : seq T) : {subset behead s <= s}.
Proof. by case: s => [ | a s] // e /=; rewrite inE orbC => ->. Qed.

Lemma contact_middle_at_point p cc s1 s2 c :
  adjacent_cells cc ->
  seq_valid cc p ->
  all (contains_point p) cc ->
  cc = s1 ++ c :: s2 ->
  (s1 != nil -> p === low c) /\ (s2 != nil -> p === high c).
Proof.
move=> adj sv ctps dec.
have cin : c \in cc by rewrite dec !(inE, mem_cat) eqxx ?orbT.
have [vlc vhc] : valid_cell c p by move: (allP sv _ cin) => /andP.
have /andP[plc phc] := (allP ctps _ cin).
split.
elim/last_ind: s1 dec => [// | s1 a _] dec _.
  have /eqP ac : high a == low c.
    case: s1 dec adj => [ | b s1] -> /=; first by move => /andP[] ->.
    by rewrite cat_path last_rcons /= => /andP[] _ /andP[].
  have ain : a \in cc by rewrite dec -cats1 !(mem_cat, inE) eqxx ?orbT.
  apply: (under_above_on vlc _ plc).
  by rewrite -ac; move: (allP ctps _ ain)=> /andP[].
case: s2 dec => [// | a s2] + _.
rewrite -[ c :: _]/([:: c] ++ _) catA => dec.
have /eqP ca : high c == low a.
  case: s1 dec adj => [ | b s1] -> /=; first by move=> /andP[] ->.
  by rewrite cats1 cat_path last_rcons /= => /andP[] _/andP[].
have ain : a \in cc by rewrite dec !(mem_cat, inE) eqxx ?orbT.
apply: (under_above_on vhc phc).
by rewrite ca; move: (allP ctps _ ain)=> /andP[].
Qed.

Lemma closing_cells_single_map p cc :
  adjacent_cells cc ->
  seq_valid cc p ->
  p >>> low (head dummy_cell cc) -> p <<< high (last dummy_cell cc) ->
  all (contains_point p) cc ->
  closing_cells p cc = map (close_cell SINGLE p) cc.
Proof.
move=> adj val pl ph ctps.
have [large | small] := boolP (1 < size cc)%N.
  have iq := closing_cells_map large val.
  have ccdq := behead_cutlasteq dummy_cell large.
  have sz :
    size (closing_cells p cc) = size [seq close_cell SINGLE p i | i <- cc].
    by rewrite [in RHS]ccdq iq /= !size_rcons !size_map size_rcons.
  have := eq_from_nth sz=> /(_ dummy_cell); apply => -[ | i].
    rewrite [in RHS] ccdq iq /= => _; apply: close_cell_equivalence_head.
    move: ccdq; rewrite -[X in cc = X]/([::] ++ [:: _] ++ _) => ccdq'.
    have [_ it] := contact_middle_at_point adj val ctps ccdq'.
    by apply: it; case: (cutlast _).
  move: (sz)=> /[swap].
  rewrite iq /= ltnS leq_eqVlt=> /orP[ | ].
    rewrite size_rcons eqSS => /eqP atend sz'.
    rewrite nth_rcons [in LHS]atend !ltnn !eqxx.
    have  : i.+1 = (size cc).-1 /\ (i.+1 < (size cc))%N.
      move: sz' large=> /eqP; rewrite -atend size_map.
      by case: (size cc) => [ | [ |  ?]] //=; rewrite eqSS => /eqP ->.
    rewrite -(size_map (close_cell SINGLE p)) => -[icc ilcc].
    rewrite (set_nth_default (close_cell SINGLE p dummy_cell) _ ilcc).
    rewrite icc nth_last last_map; apply: close_cell_equivalence_last.
    move: ccdq; rewrite -cats1 /= -cat_cons => ccdq'.
    by have [it _] := contact_middle_at_point adj val ctps ccdq'; apply: it.
  rewrite size_rcons ltnS=> inmiddle sz'.
  rewrite nth_rcons inmiddle; move: (inmiddle); rewrite size_map => inmiddle'. 
  rewrite (nth_map dummy_cell _ _ inmiddle').
  move: inmiddle; rewrite -2!ltnS sz' size_map.
  move=> /(ltn_trans (ltnSn _)) => inmiddle''.
  rewrite (nth_map dummy_cell _ _ inmiddle'') [in RHS]ccdq /=.
  rewrite nth_rcons inmiddle'.
  set protected := nth _ _ _.
  move: ccdq.
  have := mem_nth dummy_cell inmiddle'=> /splitPr[s1 s2].
  rewrite -cats1 -2!(cat_cons (head _ cc)) -!catA (cat_cons (nth _ _ _)).
  rewrite -/protected => ccdq.
  have := contact_middle_at_point adj val ctps ccdq=> -[trick trick2].
  apply: close_cell_equivalence_middle; rewrite ?trick ?trick2 //.
  by case: (s2).
move: small; case cceq: cc => [ | c [ | ? ?]] // _.
rewrite /close_cell /=.
move: val; rewrite cceq /= => /andP[] /andP[] vl vh _.
have [p1 ->] := exists_point_valid vl.
by have [p2 ->] := exists_point_valid vh.
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
  step e open closed = (open', closed') ->
  cover_left_of (point e) open closed ->
  all (lexePt p) [seq point e | e <- evs] ->
  cover_left_of p open' closed'.
Proof.
move=> sortevs cbtom adj inbox_e sval oute rfo clae clev noc btm_left stepeq.
have := step_keeps_bottom_top inbox_e sval adj cbtom oute stepeq.
have := step_keeps_adjacent inbox_e oute sval cbtom stepeq adj.
have := step_keeps_left_pts_inf inbox_e oute rfo sval adj cbtom clae
  clev noc btm_left stepeq.
have := step_keeps_closeness inbox_e oute rfo cbtom adj sval clev clae
   stepeq.
have := 
   step_keeps_valid _ inbox_e _ oute rfo cbtom adj sval clae clev _ stepeq.
move: stepeq; rewrite /step /=.
case oe : (open_cells_decomposition open (point e)) => [[[[fc cc] lc] le] he].
have subcc : {subset cc <= open}.
  by move=> x xin; rewrite (decomposition_preserve_cells oe) !mem_cat xin orbT.
move=> [] open'eq closed'eq sval0' clae' btm_left' adj' cbtom' cov limr
   q inbox_q limrq.
have [qright | qleft] := boolP(lexPt (point e) q).
  apply/orP; left.
  have [c [cin ctn]]:= exists_cell cbtom' adj' inbox_q.
  have subpq1 : subpred (lexePt p) (lexePt q).
    by move=> x px; apply/(lexePt_trans limrq).
  have limrq1 := sub_all subpq1 limr.
  have limrq' : forall e, e \in evs -> lexePt q (point e).
    by move/(sub_all subpq1): (limr); rewrite all_map=>/allP.
  have sval' := sval0' _ inbox_q qright limrq'.
  apply/hasP; exists c=> //.
  have btm_left_q : p_x (last dummy_pt (left_pts c)) <= p_x q.
    by apply/btm_left'.
  by apply: (contains_to_inside_open_cell sval' clae').
have qe : p_x q <= p_x (point e).
  by apply: lexePt_xW; rewrite lexePtNgt.
have inclosing : forall c, c \in cc -> inside_open_cell q c ->
  (forall c, c \in cc -> valid_edge (low c) (point e) &&
     (valid_edge (high c) (point e))) ->
  exists2 c', c' \in closing_cells (point e) cc & inside_closed_cell q c'.
  move=> c cin ins allval.
  have /allP ctps : forall c, c \in cc -> contains_point (point e) c.
    by move=> ?; apply: (open_cells_decomposition_contains oe).
  have [/eqP/esym lel [/eqP/esym heh _]] :=
     l_h_c_decomposition oe (exists_cell cbtom adj (inbox_e)).
  have [eabovel ebelowh] :=
        l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  have ccsub : {subset cc <= open}.
    by move=> x xin; rewrite (decomposition_preserve_cells oe) !mem_cat xin orbT.
  exists (close_cell SINGLE (point e) c).
    rewrite closing_cells_single_map => //; last first.
    - by rewrite -heh.
    - by rewrite -lel.
    - by apply/allP=> x /ccsub xin; apply: (allP sval).
    - have := adj; rewrite (decomposition_preserve_cells oe)=>/adjacent_catW.
      by move=> [] _ /adjacent_catW[].
    by apply: map_f.
  rewrite /inside_closed_cell.
  case/andP: ins=> ctn /andP[liml _] /=.
  move: ctn=>/andP [qlc qhc].
  rewrite /contains_point/close_cell /=.
  have [p1 vip1] := exists_point_valid (proj1 (andP (allval _ cin))).
  have [p2 vip2] := exists_point_valid (proj2 (andP (allval _ cin))).
  have [onl x1] := intersection_on_edge vip1.
  have [onh x2] := intersection_on_edge vip2.
  by rewrite vip1 vip2 qlc qhc /=; case: ifP => [p1e | p1ne];
    case: ifP => [p2e | p2ne]; rewrite liml /right_limit /= -?x2 -?x1.
move: qleft; rewrite -lexePtNgt lexePt_eqVlt.
have svalcc :
   forall c : cell_eqType,
     c \in cc -> valid_edge (low c) (point e) && valid_edge (high c) (point e).
   by move=> x xin; apply: (allP sval); rewrite subcc.
move=> /orP[/eqP qe' | qlte ].
  rewrite qe'.
  apply/orP; right; apply/hasP.
  set opc := head dummy_cell cc.
  have opcin : opc \in cc.
    have [_ [_ ccnnil]]:= l_h_c_decomposition oe (exists_cell cbtom adj inbox_e).
    by apply: (head_in_not_nil _ ccnnil).
  have opcin' : opc \in open by rewrite subcc.
  have leftb : p_x (last dummy_pt (left_pts opc)) <= p_x (point e).
    by apply/btm_left; rewrite subcc.
  have  : inside_open_cell (point e) opc.
    have elt : all (lexePt (point e)) [seq point e0 | e0 <- e :: evs].
      rewrite /=; rewrite lexePt_eqVlt eqxx /=.
      move: sortevs; rewrite /=; rewrite path_sortedE; last exact: lexPt_trans.
      by move=> /andP[+ _]; apply: sub_all; move=> y; apply: lexPtW.
    have : contains_point (point e) opc.
      by apply: (open_cells_decomposition_contains oe).
    by apply: (contains_to_inside_open_cell sval clae inbox_e leftb).
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

Variant marked_cell : Type := Ocell (_ : cell) | Ccell (_ : cell).

Definition marked_cell_eqb (a b : marked_cell) : bool :=
  match a, b with
  | Ocell a, Ocell b => a == b
  | Ccell a, Ccell b => a == b
  | _, _ => false
  end.

Lemma marked_cell_eqP : Equality.axiom marked_cell_eqb.
Proof.
rewrite /Equality.axiom.
move=> [a_x | a_x] [b_x | b_x] /=.
- have [/eqP <-|/eqP anb] := boolP(a_x == b_x).
    by apply: ReflectT.
  by apply: ReflectF => -[].
- by apply: ReflectF.
- by apply: ReflectF.
- have [/eqP <-|/eqP anb] := boolP(a_x == b_x).
    by apply: ReflectT.
  by apply: ReflectF => -[].
Qed.

Canonical marked_cell_eqType := EqType marked_cell (EqMixin marked_cell_eqP).

Definition unmark : marked_cell -> cell := 
  fun c => match c with Ocell x => x | Ccell x => x end.

Coercion unmark : marked_cell >-> cell.

Definition strict_inside_open (p : pt) (c : cell) :=
  (p <<< high c) && (~~(p <<= low c)) &&
  (left_limit c < p_x p < open_limit c).

Definition strict_inside_closed (p : pt) (c : cell) :=
  (p <<< high c) && (~~(p <<= low c)) &&
  (left_limit c < p_x p < right_limit c).
  
Definition strict_inside_cell (p : pt) (c : marked_cell) :=
  match c with
  | Ocell x => strict_inside_open p c
  | Ccell x => strict_inside_closed p c
  end.

Definition mark_cell_pair (s1 s2 : seq cell) :=
  [seq Ocell x | x <- s1] ++ [seq Ccell x | x <- s2]. 

Definition is_open (c : marked_cell) :=
  if c is Ccell _ then false else true.

Definition is_closed (c : marked_cell) :=
  if c is Ccell _ then true else false.

Definition unmark_cells (s : seq marked_cell) :=
  ([seq unmark c | c <- s & ~~ is_closed c], 
   [seq unmark c | c <- s & is_closed c]).

Definition sub_area (s1 s2 : marked_cell) :=
  forall p : pt, strict_inside_cell p s1 ->
                 strict_inside_cell p s2.

Definition disjoint (c1 c2 : marked_cell) :=
  forall p, ~~(strict_inside_cell p c1 && strict_inside_cell p c2).

Lemma disjointC c1 c2 : disjoint c1 c2 -> disjoint c2 c1.
Proof. by move=> c1c2 p; rewrite andbC; apply: c1c2. Qed.

Lemma disjoin_sub_area :
  forall c1 c2 c3, disjoint c1 c2 -> sub_area c3 c1 -> disjoint c3 c2.
Proof.
move=> c1 c2 c3 c1c2 c3c1 p.
apply/negP=> /andP[pc3 pc2]; case/negP:(c1c2 p).
by rewrite pc2 c3c1.
Qed.

Definition o_disjoint (c1 c2 : cell) :=
  forall p, ~~(strict_inside_open p c1 && strict_inside_open p c2).  

Definition o_disjoint_e (c1 c2 : cell) :=
  c1 = c2 \/ o_disjoint c1 c2.

Lemma o_disjointC c1 c2 : o_disjoint c1 c2 -> o_disjoint c2 c1.
Proof. by move=> c1c2 p; rewrite andbC; apply: c1c2. Qed.

Definition disjoint_open_cells :=
  forall c1 c2 : cell, o_disjoint_e c1 c2.


Lemma seq_edge_below s c :
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) ->
  path (@edge_below R) (head dummy_edge [seq low i | i <- rcons s c])
     [seq high i | i <- rcons s c].
Proof.
elim: s => [ | c0 s Ih] // /[dup]/= /adjacent_cons adj' adj /andP[] rfc rfo.
apply/andP;split;[exact: rfc | ].
have -> : high c0 = head dummy_edge [seq low i | i <- rcons s c].
  by move: adj; case: (s) => [ | c1 q]; rewrite //= => /andP[] /eqP -> _.
by apply: Ih.
Qed.

Lemma seq_edge_below' s :
  adjacent_cells s -> s_right_form s ->
  path (@edge_below R) (head dummy_edge [seq low i | i <- s])
     [seq high i | i <- s].
Proof.
elim: s => [ | c0 s Ih] // /[dup]/= /adjacent_cons adj' adj /andP[] rfc rfo.
apply/andP;split;[exact: rfc | ].
case sq : s => [// | c1 s'].
have -> : high c0 = head dummy_edge [seq low i | i <- c1 :: s'].
  by move: adj; rewrite sq /= => /andP[] /eqP.
by rewrite -sq; apply: Ih.
Qed.

Lemma below_seq_higher_edge_aux s g e p  :
  {in rcons s g & &, transitive (@edge_below R)} ->
  all (fun g' => valid_edge g' p) (rcons s g) ->
  sorted (@edge_below R) (rcons s g) ->
  all (fun g' => valid_edge g' e) (rcons s g) ->
  {in rcons s g &, no_crossing R} ->
  {in rcons s g, forall g', p <<< g' -> p <<< g}.
Proof.
elim: s => [ | g0 s Ih].
  rewrite /=?andbT => /= _ _ _ sval noc g1.
  by rewrite inE=> /eqP ->.
rewrite -[rcons _ _]/(g0 :: rcons s g)=> e_trans svp.
move/[dup]/path_sorted=> adj' adj /= sval noc.
move=> g1 g1in puc1.
have v0p : valid_edge g0 p by apply: (allP svp); rewrite inE eqxx.
have vedge g2 : g2 \in rcons s g -> valid_edge g2 p.
  by move=> g2in; apply: (allP svp); rewrite inE g2in orbT.
have vgp : valid_edge g p by apply: vedge; rewrite mem_rcons inE eqxx.
have g0below : g0 <| g.
  move: adj; rewrite /= (path_sorted_inE e_trans); last by apply/allP.
  by move=> /andP[]/allP + _; apply; rewrite mem_rcons inE eqxx.
move:g1in; rewrite /= inE => /orP[/eqP g1g0 | intail].
  by apply: (order_edges_strict_viz_point' v0p vgp g0below); rewrite -g1g0.
have tr' : {in rcons s g & &, transitive (@edge_below R)}.
  move=> g1' g2' g3' g1in g2in g3in.
  by apply: e_trans; rewrite inE ?g1in ?g2in ?g3in orbT.
have svp' : all (fun x => valid_edge x p) (rcons s g) by case/andP: svp.
have sval' : all (fun x => valid_edge x e) (rcons s g) by case/andP: sval.
have noc' : {in rcons s g &, no_crossing R}.
  by move=> g1' g2' g1in g2in; apply: noc; rewrite !inE ?g1in ?g2in orbT.
by apply: (Ih tr' svp' adj' sval' noc' g1 intail puc1).
Qed.

Definition open_cell_side_limit_ok c :=
  [&& left_pts c != [::],
   all (fun p => p_x p == p_x (last dummy_pt (left_pts c))) (left_pts c),
  sorted >%R [seq p_y p | p <- left_pts c],
  (head dummy_pt (left_pts c) === high c) &
  (last dummy_pt (left_pts c) === low c)].

Lemma strict_inside_open_valid c p :
  open_cell_side_limit_ok c ->
  strict_inside_open p  c ->
  valid_edge (low c) p && valid_edge (high c) p.
Proof.
move=> /andP[]; rewrite /strict_inside_open /left_limit /open_limit.
case: (left_pts c) => [// | w tl _] /andP[] allxl /andP[] _ /andP[].
rewrite /=; move=> /andP[] _ /andP[] lh _ /andP[] _ /andP[] ll _.
move=> /andP[] _ /andP[] ls rs.
rewrite /valid_edge ltW; last first.
  by apply: (le_lt_trans ll).
rewrite ltW; last first.
  apply: (lt_le_trans rs).
  by case: (lerP (p_x (right_pt (low c))) (p_x (right_pt (high c)))) => // /ltW.
rewrite ltW; last first.
  apply: (le_lt_trans lh).
  by rewrite (eqP (allP allxl w _)) //= inE eqxx.
apply: ltW.
apply: (lt_le_trans rs).
by case: (lerP (p_x (right_pt (low c))) (p_x (right_pt (high c)))) => // /ltW.
Qed.

Lemma valid_high_limits c p :
  open_cell_side_limit_ok c ->
  left_limit c < p_x p < open_limit c -> valid_edge (high c) p.
Proof.
move=>/andP[] wn0 /andP[] /allP allx /andP[] _ /andP[] /andP[] _ /andP[] + _ _.
rewrite (eqP (allx _ (head_in_not_nil _ wn0))) // => onh.
rewrite /left_limit=> /andP[] /ltW llim /ltW.
rewrite /valid_edge (le_trans onh llim) /=.
rewrite /open_limit.
case: (lerP (p_x (right_pt (low c))) (p_x (right_pt (high c))))=> // /[swap].
by apply: le_trans.
Qed.

Lemma valid_low_limits c p :
  open_cell_side_limit_ok c ->
  left_limit c < p_x p < open_limit c -> valid_edge (low c) p.
Proof.
move=>/andP[] wn0 /andP[] /allP allx /andP[] _ /andP[] _ /andP[] _ /andP[] onl _.
rewrite /left_limit=> /andP[] /ltW llim /ltW.
rewrite /valid_edge (le_trans onl llim) /=.
rewrite /open_limit.
case: (lerP (p_x (right_pt (low c))) (p_x (right_pt (high c))))=> // /[swap].
by move=> ph hl; apply/ltW/(le_lt_trans ph hl).
Qed.

Lemma opening_cells_aux_side_limit e s le he :
  valid_edge le e -> valid_edge he e -> le <| he ->
  e >>= le -> e <<< he ->
  {in [:: le, he & s] &, no_crossing R} ->
  {in s, forall g, left_pt g == e} ->
  all open_cell_side_limit_ok (opening_cells_aux e s le he).
Proof.
move=> + vh.
elim : s le=> [ | g s Ih] le /= vl lowhigh above under noc lg;
   set vip := vertical_intersection_point.
  case vip1 : vip => [p1 | //]; case vip2 : vip => [p2 | //].
  apply/allP=> c; rewrite inE /open_cell_side_limit_ok => /eqP -> /=.
  have [v1 on1 x1] : [/\ valid_edge le p1, p1 === le & p_x e = p_x p1].
    have [on1 xp] := intersection_on_edge vip1; split => //.
    rewrite /valid_edge -xp; exact vl.
  have [v2 on2 x2] : [/\ valid_edge he p2, p2 === he & p_x e = p_x p2].
    have [on2 xp] := intersection_on_edge vip2; split => //.
    rewrite /valid_edge -xp; exact vh.
  have p2ne : p2 != e.
    apply/eqP=> A; have := strict_under_edge_lower_y x2 on2.
    by rewrite under => /esym; rewrite ltNge A lexx.
  rewrite (negbTE p2ne); case: ifP => [p1ise | p1ne] /=;
    move: on1 on2; rewrite ?(eqP p2ise) -?(eqP p1ise) => on1 on2;
    rewrite ?eqxx ?on1 ?on2 ?(eqP p2ise) -?(eqP p1ise) -?x1 -?x2
        ?eqxx ?andbT //=.
  - have euh : e <<= he.
      apply: (order_edges_viz_point' vl)=> //.
      move: on1; rewrite /point_on_edge /point_under_edge=>/andP[]/eqP -> _.
      by rewrite lexx.
    rewrite lt_neqAle -(under_edge_lower_y x2 on2) euh andbT.
    by apply/negP=> A; case/negP: p2ne; rewrite pt_eqE (eqP A) x2 ?eqxx.
  rewrite -(strict_under_edge_lower_y x2 on2) under /=.
  rewrite ltNge le_eqVlt negb_or.
  rewrite -(strict_under_edge_lower_y x1 on1) above andbT.
  by apply/negP=> A;case/negbT/negP:p1ne; rewrite pt_eqE -?x1 (eqP A) !eqxx.
have /eqP lgg : left_pt g == e by apply: lg; rewrite inE eqxx.
case vip1 : vip => [p1 | //].
have [v1 on1 x1] : [/\ valid_edge le p1, p1 === le & p_x e = p_x p1].
  have [on1 xp] := intersection_on_edge vip1; split => //.
  rewrite /valid_edge -xp; exact vl.
have eong : e === g by rewrite -(eqP (lg g _)) ?inE ?eqxx // left_on_edge.
apply/allP=> c; rewrite inE=> /orP[/eqP -> | cintl].
  rewrite /open_cell_side_limit_ok.
  case: ifP=> [eisp1 | enp1] /=;
    rewrite -?x1 !eqxx on1 -?(eqP eisp1) ?eong ?andbT //=.
  rewrite ltNge le_eqVlt negb_or.
  rewrite -(strict_under_edge_lower_y x1 on1) above andbT.
  by apply/negP=> A; case/negP: enp1; rewrite pt_eqE (eqP A) x1 ?eqxx.
suff/allP/(_ c cintl) :
   all open_cell_side_limit_ok (opening_cells_aux e s g he).
  by [].
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
apply: opening_cells_aux_side_limit => //; last first.
  move=> g; rewrite (perm_mem (permEl (perm_sort _ _))); apply: lefts.
move=> g1 g2; rewrite !inE !(perm_mem (permEl (perm_sort _ _)))=> g1in g2in.
by apply: noc.
Qed.

Lemma below_seq_higher_edge s c e p :
  {in [seq high i | i <- rcons s c] & & ,transitive (@edge_below R)} ->
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) -> 
  seq_valid (rcons s c) e -> 
  {in [seq high i | i <- rcons s c] &, no_crossing R} ->
  {in rcons s c, forall g, open_cell_side_limit_ok g} ->
  {in rcons s c, forall c1, strict_inside_open p c1 ->
                 valid_edge (high c) p-> p <<< high c}.
Proof.
move=> e_trans adj rf sval noc csok c1 c1in /[dup]/andP[] /andP[] puc1 _ pp2.
move=> inpc1.
set g := high c => vgp.
set sg := [seq high i | i <- s & valid_edge (high i) p].
have subp : {subset rcons sg g <= [seq high i | i <- rcons s c]}.
  move=> g1; rewrite map_rcons 2!mem_rcons 2!inE=>/orP[-> //| ].
  rewrite /sg=> /mapP[c1' + c1'eq]; rewrite mem_filter=>/andP[] _ c1'in.
  by apply/orP; right; apply/mapP; exists c1'.
have e_trans' : {in rcons sg g & &, transitive (@edge_below R)}.
  move=> g1 g2 g3 g1in g2in g3in.
  by apply: e_trans; apply: subp.
have svp : all (fun g' => valid_edge g' p) (rcons sg g).
  apply/allP=> g'; rewrite -map_rcons => /mapP [c' + ->].
  by rewrite mem_rcons inE mem_filter => /orP[/eqP -> |  /andP[] + _].
have adj' : sorted (@edge_below R) (rcons sg g).  
  have sggq : rcons sg g =
             [seq i  <- [seq high j | j <- rcons s c] | valid_edge i p].
     by rewrite (@filter_map _ _ high) filter_rcons /= vgp map_rcons.
  rewrite sggq.
  apply: (sorted_filter_in e_trans).
    apply/allP=> g1 /mapP[c' + g'eq]. 
    rewrite -[pred_of_seq _ g1]/(g1 \in map _ _) !mem_rcons !inE.
    rewrite /g=>/orP[/eqP <- | c'in].
      by rewrite map_rcons mem_rcons inE g'eq eqxx.
    by rewrite map_rcons mem_rcons inE; apply/orP/or_intror/mapP; exists c'.
  have := seq_edge_below' adj rf.
  by case s_eq : s => [ // | a s' /=] /andP[] _.
have noc' : {in rcons sg g &, no_crossing R}.
  by move=> g1 g2 /subp g1in /subp g2in;  apply: noc.
apply: (below_seq_higher_edge_aux e_trans' svp adj' svp noc' _ puc1).
rewrite -map_rcons; apply/mapP; exists c1 => //.
move: c1in; rewrite !mem_rcons !inE=>/orP[-> // | c1in].
rewrite mem_filter c1in andbT; apply/orP/or_intror.
apply: (proj2 (andP (strict_inside_open_valid _ inpc1))).
by apply: csok; rewrite mem_rcons inE c1in orbT.
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
move=> lowhigh ebounds vle vhe vp gleft noc oc /andP[]/andP[] plhc _ plim.
move: (ebounds) => /andP[] above under.
have labove : e >>= le by rewrite -leNgt ltW // ltNge; exact: above.
have := opening_cells_subset oc => /andP[] _.
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
by apply: valid_high_limits cok plim.
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
move=> lowhigh ebounds vle vhe vp gleft noc oc /andP[]/andP[] _ palc plim.
move: (ebounds) => /andP[] above under.
have labove : e >>= le by rewrite -leNgt ltW // ltNge; exact: above.
have := opening_cells_subset oc => /andP[] + _.
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
by apply: (valid_low_limits cok).
Qed.

Lemma left_side_below_seq_higher_edge s c e p :
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) ->
  seq_valid (rcons s c) e ->
  {in [seq high i | i <- rcons s c], forall g, p_x (left_pt g) < p_x e} ->
  {in [seq high i | i <- rcons s c] &, no_crossing R} ->
  {in rcons s c, forall c1, open_cell_side_limit_ok c1} ->
  {in rcons s c, forall c1, strict_inside_open p c1 ->
        valid_edge (high c) p -> p <<< high c}.
Proof.
move => adj rfs svals llim noc csok.
apply: (below_seq_higher_edge _ adj rfs svals) => //.
have vale' : {in [seq high i | i <- rcons s c], forall g, valid_edge g e}.
  by move=> g /mapP [c' c'in ->]; move: (allP svals c' c'in)=>/andP[].
apply: (edge_below_trans _ vale' noc); right; exact: llim.
Qed.

Lemma right_side_below_seq_higher_edge s c e p :
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) -> 
  seq_valid (rcons s c) e ->
  {in [seq high i | i <- rcons s c], forall g, p_x e < p_x (right_pt g)} ->
  {in [seq high i | i <- rcons s c] &, no_crossing R} ->
  {in rcons s c, forall c1, open_cell_side_limit_ok c1} ->
  {in rcons s c, forall c1, strict_inside_open p c1 -> 
      valid_edge (high c) p -> p <<< high c}.
Proof.
move => adj rfs svals (* clae *) rlim noc csok.
apply: (below_seq_higher_edge _  adj rfs svals) => //.
have vale' : {in [seq high i | i <- rcons s c], forall g, valid_edge g e}.
  by move=> g /mapP [c' c'in ->]; move: (allP svals c' c'in)=>/andP[].
apply: (edge_below_trans _ vale' noc); left; exact: rlim.
Qed.

Lemma o_disjoint_eC (c1 c2 : cell) :
  o_disjoint_e c1 c2 -> o_disjoint_e c2 c1.
Proof.
move=> [-> // |]; first by left.
by move=> disj; right=> p; rewrite andbC; apply: disj.
Qed.

Lemma opening_cells_aux_disjoint (s oe : seq edge) p le he :
    p >>> le -> p <<< he -> le \in s -> he \in s -> le <| he ->
    valid_edge le p -> valid_edge he p -> {subset oe <= s} ->
    {in s &, no_crossing R} -> {in oe, forall g : edge, left_pt g == p} ->
    path (@edge_below R) le oe ->
    {in opening_cells_aux p oe le he &, disjoint_open_cells}.
Proof.
move=> pl ph lein hein lowhigh vl vh oesub noc leftg soe.
have {}pl : p >>= le by apply/negP=> pule; case/negP: pl; apply: underW.
elim: oe oesub leftg le lowhigh pl lein vl soe
   => [ | og oe Ih] oesub leftg le lowhigh pl lein vl soe.
  rewrite /=; case vip1 : (vertical_intersection_point _ _) => [p1 |// ].
  case vip2 : (vertical_intersection_point _ _) => [p2 |// ].
  by move=> c1 c2; rewrite !inE /= => /eqP -> /eqP ->; left.
rewrite /=; case vip : (vertical_intersection_point _ _) => [p1 |//].
set W := Bcell _ _ _ _.
have /eqP logp : left_pt og == p by apply/leftg; rewrite inE eqxx.
suff main : forall c, c \in opening_cells_aux p oe og he -> o_disjoint_e W c.
  move=> c1 c2; rewrite !inE => /orP[/eqP c1W |c1in] /orP[/eqP c2W | c2in].
  - by left; rewrite c1W c2W.
  - by rewrite c1W; apply: main.
  - by rewrite c2W; apply/o_disjoint_eC/main.
  apply: (Ih _ _ og) => //.
  - by move=> x xin; rewrite oesub // inE xin orbT.
  - by move=> x xin; rewrite leftg // inE xin orbT.
  - have ogin : og \in s by rewrite oesub // inE eqxx.
    have := no_crossingE (noc _ _  ogin hein); rewrite logp vh ph.
    by move=> /(_ isT)[]/(_ isT).
  - by rewrite -(eqP (leftg og _)) ?left_pt_above // inE eqxx.
  - by rewrite oesub // inE eqxx.
  - by rewrite valid_edge_extremities // leftg ?inE ?eqxx.
  by move: soe=> /=/andP[] _.
move=> c cin; right=> q.
have oc0q : opening_cells_aux p (og :: oe) le he =
   W :: opening_cells_aux p oe og he.
  by rewrite /= vip.
have noc' : {in [:: le, he , og & oe] &, no_crossing R}.
  move: noc; apply: sub_in2 => g; rewrite 2!inE.
  by move=> /orP[/eqP ->| /orP[/eqP -> | ginoe]] //; apply: oesub.
have/allP cok := opening_cells_aux_side_limit vl vh lowhigh pl ph noc' leftg.
have [/andP[]/andP[] Main w lims/= | qnW//] := boolP(strict_inside_open q W).
have vhwq : valid_edge (high W) q.
  apply: valid_high_limits => //.
  by apply: cok; rewrite oc0q inE eqxx.
have adj0 := adjacent_opening' p (og :: oe) le he.
have rf0 := opening_cells_aux_right_form pl ph vh lein hein lowhigh leftg noc
         oesub soe.
have := seq_edge_below' adj0 rf0; rewrite oc0q [head _ _]/= => srt.
have vog : valid_edge og q by move: vhwq; rewrite [high W]/=.
case ocq : (opening_cells_aux p oe og he) => [| c0 q0].
  by move: cin; rewrite ocq.
move: adj0; rewrite /= ocq vip /= => /andP[/eqP ogl adj'].
move: vog; rewrite ogl=> vog.
move: (cin) => /(nthP W) [rank rltsize /esym ceq].
have {}ceq : c = nth W (c0 :: q0) rank by move: ceq; rewrite ocq.
case rankeq: rank => [ | rank'].
  have cc0 : c = c0 by rewrite ceq rankeq.
  move: Main; rewrite /W /= => Main.
  by rewrite /strict_inside_open cc0 -ogl underW ?andbF.
have cq0 : c \in q0.
  have/(mem_nth W) : (rank' < size q0)%N.
    by rewrite -ltnS -[(size _).+1]/(size (c0 :: q0)) -ocq -rankeq.
  by rewrite -[nth _ _ _]/(nth W (c0::q0) rank'.+1) -rankeq -ceq.
apply/negP; rewrite /strict_inside_open => inc.
have valq : valid_edge (low c) q.
  apply: valid_low_limits.
    by apply: cok; rewrite oc0q ocq !inE cq0 ?orbT.
  by move: inc=> /andP[] _ //.
have tr : {in (og :: oe) & & , transitive (@edge_below R)}.
  apply: (@edge_below_trans R p); last by move: noc; apply: sub_in2.
    by left; move=> g gin; rewrite -(eqP (leftg g gin)) edge_cond.
  by move=> g gin; apply: valid_edge_extremities; rewrite leftg ?eqxx.
have  : all (mem (og :: oe)) [seq low i | i <- opening_cells_aux p oe og he].
  apply/allP=> g /mapP [c2 c2p1 ->].
  by have := opening_cells_aux_subset c2p1=> /andP[].
have vog' : valid_edge og p.
  by rewrite valid_edge_extremities // (leftg og) ?inE ?eqxx.
rewrite ocq /==> allid.
have := path_sorted_inE tr allid => patheq.
have leftg' : {in oe, forall g, left_pt g == p}.
  by move: leftg; apply: sub_in1=> g' gin; rewrite inE gin orbT.
move: srt; rewrite [X in path _ _ X]/= opening_cells_seq_edge_shift //.
rewrite ocq /= -cats1 cat_path -ogl => /andP[] _ /andP[].
rewrite ogl patheq -ogl => /andP[] /allP /(_ (low c)) pathconcl _ _.
have lowcin : low c \in [seq low i | i <- q0] by apply: map_f.
have qu:= order_edges_strict_viz_point' vhwq valq (pathconcl lowcin) Main.
by move: inc; rewrite (underW qu) !andbF.
Qed.

Definition closed_cell_side_limit_ok c :=
 [&& left_pts c != [::],
   all (fun p : pt => p_x p == p_x (last dummy_pt (left_pts c))) (left_pts c),
   sorted >%R [seq p_y p | p <- left_pts c],
   head dummy_pt (left_pts c) === high c,
   last dummy_pt (left_pts c) === low c,
    right_pts c != [::],
   all (fun p : pt => p_x p == p_x (head dummy_pt (right_pts c))) (right_pts c),
   sorted <%R [seq p_y p | p <- right_pts c],
   head dummy_pt (right_pts c) === low c &
   last dummy_pt (right_pts c) === high c].

Lemma closing_rest_side_limit e cc :
  (cc != nil -> e === low (head dummy_cell cc)) ->
  s_right_form cc ->
  seq_valid cc e ->
  adjacent_cells cc ->
  all open_cell_side_limit_ok cc ->
  all (contains_point e) cc ->
  all closed_cell_side_limit_ok (closing_rest e cc).
Proof.
apply closing_rest_ind=> //.
  move=> c p1 vip /=.
  move=> /(_ isT) elow /andP[] rf0 _ _ _ /andP[] lim0 _ /andP[] ct0 _.
  move: lim0=> /andP[] ln0 /andP[] lxs /andP[] ls /andP[] onh onl.
  have [onhr x1] := intersection_on_edge vip.
  case: ifP => [/eqP eisp1 | enp1];
    rewrite /closed_cell_side_limit_ok ln0 lxs ls onh onl onhr /= 
       ?eqxx ?andbT /=.
    by rewrite -eisp1.
  rewrite x1 elow ?andbT eqxx /=.
  have vh : valid_edge (high c) e.
    by move: onhr=>/andP[] _; rewrite /valid_edge x1.
  move: ct0 => /andP[] _; rewrite (under_onVstrict vh)=> /orP[eh|]; last first.
    by rewrite (strict_under_edge_lower_y x1 onhr).
  by case/negP: enp1; rewrite pt_eqE (on_edge_same_point eh onhr) x1 eqxx.
move=> c a q Ih /(_ isT) elow.
rewrite /= in elow; rewrite /s_right_form.
have simpall (f : cell -> bool) y tl : all f (y :: tl) = f y && all f tl by [].
rewrite !(simpall _ c)=> /andP[]rfc rfa sval adj/andP[]limc lima /andP[]ctc cta.
have adjca : high c = low a by move: adj=> /andP[]/eqP.
have eh : e === high c.
  move: ctc cta=> /= + /andP[]+ _; rewrite /contains_point.
  rewrite adjca=> /andP[] _ under /andP[] above _.
  by apply under_above_on => //; move: sval=> /andP[] _ /andP[] /andP[].
rewrite simpall; apply/andP; split; last first.
  apply: Ih => //.
  - by rewrite /= -adjca.
  - by move: sval; rewrite /= => /andP[].
  by apply: (adjacent_cons adj).
rewrite /closed_cell_side_limit_ok /=.
move: limc=> /andP[] ln0 /andP[] lxs /andP[]ls /andP[]onlh onll.
by rewrite ln0 lxs ls onlh onll eqxx elow/=.
Qed.

Lemma closing_cells_side_limit e cc :
  s_right_form cc ->
  seq_valid cc e ->
  adjacent_cells cc ->
  all open_cell_side_limit_ok cc ->
  all (contains_point e) cc ->
  all closed_cell_side_limit_ok (closing_cells e cc).
Proof.
set vip := vertical_intersection_point.
case: cc => [ // | c0 [| c1 q]];
move=> /andP[] rf0 rfr /andP[] /andP[] vl vh sv adj /andP[] lim0 limr /andP[]
  ct0 ctr.
  rewrite -/vip; move: rf0 lim0.
  rewrite /open_cell_side_limit_ok => lowhigh /andP[] ln0.
  move=> /andP[] lxs /andP[] ls /andP[] onh onl.
  rewrite /= -/vip; case vip1 : vip => [p1 | //]; case vip2: vip => [p2 /=| //];
  have [onlr x1] := intersection_on_edge vip1;
  have [onhr x2] := intersection_on_edge vip2.
  rewrite /closed_cell_side_limit_ok /= ln0 lxs ls onh onl /=.
  case: ifP=> [/eqP p1ise | p1ne]; case: ifP=> [/eqP eisp2 | enp2] /=;
    rewrite ?eqxx ?onhr ?onlr.
  - by rewrite -eisp2 -p1ise onlr.
  - rewrite x2 eqxx (_ : e === low c0); last by rewrite -p1ise.
    move: ct0; rewrite /contains_point under_onVstrict // => /andP[] _.
    move/orP=> [ | str]; last first.
      by rewrite -(strict_under_edge_lower_y x2 onhr) str.
    move=> eoh; have := on_edge_same_point eoh onhr => tmp.
    by case/negP: enp2; rewrite pt_eqE tmp x2 eqxx.
  - rewrite -x2 x1 eqxx.
    move: ct0; rewrite /contains_point strict_nonAunder // => /andP[] + _.
    rewrite negb_and negbK=>/orP [ | str]; last first.
      have p1p2 : p_x p1 = p_x p2 by rewrite -x1.
    by rewrite /= !andbT ltNge -(under_edge_lower_y (esym p1p2) onlr) -eisp2.
    move=> eol; have := on_edge_same_point eol onlr => tmp.
    by case/negP: p1ne; rewrite eq_sym pt_eqE tmp x1 eqxx.
  rewrite /= ?andbT x1 eqxx -x2 x1 eqxx /=.
  move: ct0; rewrite /contains_point strict_nonAunder // => /andP[] + under2.
  rewrite negb_and negbK=> /orP[eol| ]; last first.
    rewrite (under_edge_lower_y x1 onlr) -ltNge => -> /=.
    move: under2; rewrite under_onVstrict // => /orP[eoh| ]; last first.
      by rewrite (strict_under_edge_lower_y x2 onhr).
    have := on_edge_same_point onhr eoh => {}eoh; case/negP:enp2.
    by rewrite eq_sym pt_eqE eoh x2 eqxx.
  have := on_edge_same_point onlr eol => {}eol; case/negP:p1ne.
  by rewrite pt_eqE eol x1 eqxx.
rewrite /= -/vip; case vip1: (vip _ _) => [p1 |// ].
have [onl x1 ]:= intersection_on_edge vip1.
have adj' : adjacent_cells (c1 :: q) by exact: (adjacent_cons adj).
have lowhigh : high c0 = low c1 by move: adj=> /andP[]/eqP ->.
have eloc1 : e === low c1.
  move: ct0=>/andP[] _ eh; move: ctr=>/andP[] /andP[] + _ _.
  rewrite -lowhigh=> eh'.
  by apply: under_above_on.
rewrite allcons; apply/andP; split; last first.
  rewrite -[X in all _ X]/(closing_rest e (c1 :: q)).
  by apply: closing_rest_side_limit.
move: lim0=>/andP[]ln0 /andP[] lxs /andP[] ls /andP[] onlh onll.
rewrite /closed_cell_side_limit_ok /= ln0 lxs ls onlh onll /=.
case: ifP => [/eqP p1ise | p1ne] /=; rewrite eqxx.
  by move: onl; rewrite p1ise=> -> /=; rewrite lowhigh.
rewrite x1 onl lowhigh eloc1 eqxx ?andbT /=.
move: ct0=> /andP[] + _; rewrite strict_nonAunder // negb_and negbK.
move: eloc1; rewrite -lowhigh => ehi0.
rewrite (under_edge_lower_y x1 onl) -ltNge => /orP[|//].
move=> eloc0; case/negP: p1ne; rewrite eq_sym.
have := on_edge_same_point eloc0 onl; rewrite x1 => /(_ (eqxx _)) ys.
by rewrite pt_eqE ys x1 eqxx.
Qed.

Lemma close_cell_ok v e c :
  contains_point e c ->
  (v = HEAD -> e === high c) ->
  (v = MIDDLE -> e === low c /\ e === high c) ->
  (v = LAST -> e === low c) ->
  valid_edge (low c) e -> valid_edge (high c) e ->
  open_cell_side_limit_ok c ->
  closed_cell_side_limit_ok (close_cell v e c).
Proof.
move=> ctp hea mid las vl vh.
rewrite /open_cell_side_limit_ok/closed_cell_side_limit_ok.
rewrite /close_cell /=; have /exists_point_valid [p1 /[dup] vip1 ->] := vl.
have /exists_point_valid [p2 /[dup] vip2 -> /=] := vh.
move=> /andP[] -> /andP[]-> /andP[]-> /andP[] -> -> /=.
have [o1 x1]:=intersection_on_edge vip1; have [o2 x2]:=intersection_on_edge vip2.
case vq: v hea mid las;[move=> _ _ _ | move=> + _ _| move=> _ + _| move=> _ _ +];
 rewrite /=; rewrite -?(eq_sym e).
- case:ifP=>[/eqP q1 | enp1];case:ifP=>[/eqP q2 | enp2]; move: (o1) (o2);
  rewrite /=  -?q1 -?q2 -?x1 -?x2 ?eqxx/= => -> ->; rewrite ?andbT //=.
  * move: ctp=> /andP[] _ eh.
    by apply: (under_edge_strict_lower_y x2 (negbT enp2) eh).
  * move: ctp=> /andP[] el _.
    by apply: (above_edge_strict_higher_y x1 (negbT enp1) el).
  move: ctp=> /andP[] el eh.
  by rewrite (above_edge_strict_higher_y x1 (negbT enp1) el) //
      (under_edge_strict_lower_y x2 (negbT enp2) eh).
- move=> /(_ erefl) eh; move: ctp=> /andP[] el eh' /=.
  case: ifP=>[/eqP q1| enp1]; move: (o1);
  rewrite /=  -?q1 -?q2 -?x1 -?x2 ?eqxx ?eh'/= => ->; rewrite ?andbT //.
  by rewrite (above_edge_strict_higher_y x1 (negbT enp1) el).
- by move=> /(_ erefl) [-> ->]; rewrite eqxx.
move=> /(_ erefl) el; move: ctp => /andP[] _ eh.
case: ifP=>[/eqP q1| enp2]; move: (o2);
  rewrite /=  -?q1 -?q2 -?x1 -?x2 ?eqxx ?eh'/= => ->; rewrite ?andbT //.
by rewrite el (under_edge_strict_lower_y x2 (negbT enp2) eh).
Qed.

Lemma closing_cells_side_limit' e cc :
  s_right_form cc ->
  seq_valid cc e ->
  adjacent_cells cc ->
  all open_cell_side_limit_ok cc ->
  all (contains_point e) cc ->
  all closed_cell_side_limit_ok (closing_cells e cc).
Proof.
move=> rf val adj oks ctps.
have [large | small] := boolP (1 < size cc)%N.
  have iq := closing_cells_map large val.
  have ccdq := behead_cutlasteq dummy_cell large.
 have hin : head dummy_cell cc \in cc.
   by apply/head_in_not_nil/eqP=> abs; move: large; rewrite abs.
 have lin : last dummy_cell cc \in cc.
   by apply/last_in_not_nil/eqP=> abs; move: large; rewrite abs.
  have ehh : e === high (head dummy_cell cc).
    move: ccdq; set w := rcons _ _ => ccdq.
    have wn0 : w != nil by rewrite /w; case: (cutlast _).
    have := contact_middle_at_point adj val ctps=> /(_ nil w _ ccdq)[] _.
    by apply.
  have ell : e === low (last dummy_cell cc).
    move:ccdq; rewrite -cats1 -cat_cons; set w := (X in X ++ _) => ccdq.
    have := contact_middle_at_point adj val ctps=> /(_ w nil _ ccdq)[] + _.
    by apply.
  apply/allP=> c; rewrite iq inE=> /orP[/eqP cc0| ].
    rewrite cc0; apply: close_cell_ok => //.
    - by apply: (allP ctps).
    - by move: (allP val _ hin)=> /andP[].
    - by move: (allP val _ hin)=> /andP[].
    by apply: (allP oks).
  rewrite -cats1 mem_cat=> /orP[]; last first.
    rewrite inE => /eqP ->; apply: close_cell_ok => //.
    - by apply: (allP ctps).
    - by move: (allP val _ lin)=> /andP[].
    - by move: (allP val _ lin)=> /andP[].
    by apply: (allP oks).
  move=> /mapP[c' cin ->].
  move: (cin) (ccdq); case/splitPr => s1 s2.
  rewrite -cats1 -2!(cat_cons (head _ _)) -catA (cat_cons c') cats1.
  set w1 := (head _ _ :: _); set w2 := (rcons _ _)=> ccdq'.
  have c'in2 : c' \in cc by rewrite ccdq' !(inE, mem_cat) eqxx ?orbT.
  have [w1n0 w2n0] : w1 != nil /\ w2 != nil by rewrite // /w2; case: (s2).
  have [el' eh'] : e === low c' /\ e === high c'.
    have := contact_middle_at_point adj val ctps ccdq'.
    by move=> -[]/(_ w1n0) + /(_ w2n0).
  apply: close_cell_ok => //.
  - by apply: (allP ctps); rewrite behead_subset // cutlast_subset.
  - by move: (allP val _ c'in2)=>/andP[].
  - by move: (allP val _ c'in2)=>/andP[].
  by apply: (allP oks); rewrite behead_subset // cutlast_subset.
case sq : cc small => [ | c [ | ? ?]] // _.
rewrite closing_cell1; last by rewrite -sq.
rewrite allcons andbT; apply: close_cell_ok => //.
- by move: ctps; rewrite sq /= andbT.
- by move: val; rewrite sq /= andbT=>/andP[] .
- by move: val; rewrite sq /= andbT=>/andP[] .
by move: oks; rewrite sq /= andbT.
Qed.

Lemma closed_right_imp_open c:
  closed_cell_side_limit_ok c -> right_limit c <= open_limit c.
Proof.
move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
move=> /andP[] ln0 /andP[] eqs /andP[] _ /andP[] /andP[] _ /andP[] _ /[swap].
move=> /andP[] _ /andP[] _.
rewrite /right_limit /open_limit.
rewrite -(eqP (allP eqs (last dummy_pt (right_pts c)) (last_in_not_nil _ ln0))).
by case : (lerP (p_x (right_pt (low c))) (p_x (right_pt (high c)))).
Qed.

Lemma open_limit_close_cell v p c :
  open_limit (close_cell v p c) = open_limit c.
Proof.
rewrite /close_cell.
case : (vertical_intersection_point p (low c)) => [p1 | ]//.
by case : (vertical_intersection_point p (high c)) => [p2 | ].
Qed.

Lemma close_cell_subset_contact v p q c :
  valid_cell c p -> 
  closed_cell_side_limit_ok (close_cell v p c) ->
  strict_inside_closed q (close_cell v p c) -> strict_inside_open q c.
Proof.
move=>[] vl vh.
move=>/closed_right_imp_open.
rewrite /strict_inside_closed/strict_inside_open/close_cell.
have [p1 vip1] := exists_point_valid vl.
have [p2 vip2] := exists_point_valid vh.
rewrite vip1 vip2 /= => cok /andP[]/andP[] -> -> /andP[] -> rlim /=.
by apply: (lt_le_trans rlim cok).
Qed.

(* The same function but for marked cells, does erases previous closing
 data if the cell is already closed *)
Definition mclose_cell p (c : marked_cell) :=
  Ccell (close_cell SINGLE p c).

Lemma mclosed_cell_sub s p :
  seq_valid [seq unmark c | c <-s] p ->
  all (contains_point p) [seq unmark c | c <-s] ->
  all open_cell_side_limit_ok [seq unmark c | c <-s] ->
  all is_open s ->
  {in (mem s), forall c, sub_area (mclose_cell p c) c}.
Proof.
move=> sval ctps oks ope.
move=> [ c | c] cin; last by have := (allP ope _ cin).
have cin' : c \in [seq unmark c | c <- s].
  by apply/mapP; exists (Ocell c).
have vc : valid_cell c p.
  by apply/andP; apply: (allP sval).
rewrite /mclose_cell /sub_area /= => q; apply: close_cell_subset_contact => //.
apply: close_cell_ok => //.
- by apply: (allP ctps).
- by case: vc.
- by case: vc.
by apply: (allP oks).
Qed.

Section abstract_subsets_and_partition.

Variable sub : cell -> cell -> Prop.
Variable exclude : cell -> cell -> Prop.

Variable close : cell -> cell.

Hypothesis excludeC : forall c1 c2, exclude c1 c2 -> exclude c2 c1.
Hypothesis exclude_sub : 
  forall c1 c2 c3, exclude c1 c2 -> sub c3 c1 -> exclude c3 c2.

Lemma add_map (s1 : pred cell) (s2 : seq cell) :
    all (predC s1) s2 ->
    {in s2, forall c, sub (close c) c} ->
    {in predU s1 (mem s2) &, forall c1 c2, c1 = c2 \/ exclude c1 c2} ->
  {in predU s1 (mem [seq close c | c <- s2]) &,
    forall c1 c2, c1 = c2 \/ exclude c1 c2}.
Proof.
have symcase : forall (s : pred cell) (s' : seq cell),
  all (predC s) s' -> 
  {in s', forall c, sub (close c) c} ->
  {in predU s (mem s') &, forall c1 c2, c1 = c2 \/ exclude c1 c2} ->
  forall c1 c2, s c1 -> c2 \in s' -> exclude c1 (close c2).
  move=> s s' dif clsub exc c1 c2 sc1 c2s'.
  apply/excludeC/(exclude_sub _ (clsub _ _)); last by [].
  have := exc c2 c1; rewrite 2!inE c2s' orbT inE sc1 => /(_ isT isT).
  by move=> -[abs | //]; have := allP dif _ c2s'; rewrite inE abs sc1.
move=> s1nots2 clsub oldx g1 g2.
rewrite inE => /orP[g1old | /mapP[co1 co1in g1c]];
  rewrite inE =>  /orP[g2old |/mapP[co2 co2in g2c ]].
- by apply: oldx; rewrite inE ?g1old ?g2old.
- by right; rewrite g2c; apply: (symcase _ _ s1nots2 clsub oldx).
- by right; rewrite g1c; apply excludeC; apply: (symcase _ _ s1nots2 clsub oldx).
have [/eqP co1co2 | co1nco2] := boolP(co1 == co2).
  by left; rewrite g1c g2c co1co2.
right; rewrite g1c; apply/(exclude_sub _ (clsub _ _)); last by [].
rewrite g2c; apply/excludeC/(exclude_sub _ (clsub _ _)); last by [].
have := oldx co2 co1; rewrite !inE co2in co1in !orbT=> /(_ isT isT).
by case=> [abs | //]; case/negP: co1nco2; rewrite abs eqxx.
Qed.

Lemma add_new (s s2 : pred cell) :
  {in s &, forall c1 c2, c1 = c2 \/ exclude c1 c2} ->
  {in s & s2, forall c1 c2, exclude c1 c2} ->
  {in s2 &, forall c1 c2, c1 = c2 \/ exclude c1 c2} ->
  {in predU s s2 &, forall c1 c2, c1 = c2 \/ exclude c1 c2}.
Proof.
move=> oldx bipart newx c1 c2.
rewrite inE=> /orP[c1old | c1new] /orP[c2old | c2new].
- by apply: oldx.
- by right; apply: bipart.
- by right; apply/excludeC/bipart.
by apply: newx.
Qed.

End abstract_subsets_and_partition.

Lemma out_left_event_on e :
  out_left_event e -> {in outgoing e, forall g, point e === g}.
Proof.
move=> outs g gin; rewrite -(eqP (outs _ gin)); apply: left_on_edge.
Qed.

Lemma sorted_outgoing le he e : 
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  point e >>> le ->
  point e <<< he ->
  out_left_event e ->
  {in le :: he :: outgoing e &, no_crossing R} ->
  sorted (@edge_below R) (le :: sort (@edge_below R) (outgoing e)).
Proof.
 set ctxt := (le :: he :: _); move=> vl hl above under outs noc.
have lein : le \in ctxt by rewrite /ctxt inE eqxx.
have hein : he \in ctxt by rewrite /ctxt !inE eqxx ?orbT.
have osub : {subset outgoing e <= ctxt}.
  by move=> g gin; rewrite /ctxt !inE gin ?orbT.
have [ls us noc''] :=
   outgoing_conditions above under lein hein vl hl osub noc outs.
have /sort_sorted_in tmp : {in le :: outgoing e &, total (@edge_below R)}.
  move=> e1 e2; rewrite !inE =>/orP[/eqP -> |e1in ]/orP[/eqP -> |e2in].
  - by rewrite edge_below_refl.
  - by rewrite ls.
  - by rewrite ls ?orbT.
  by apply/orP/noc''.
rewrite /=; case oeq : (sort (@edge_below R) (outgoing e)) => [// | g1 gs] /=.
rewrite ls; last first.
  have <- := perm_mem (permEl (perm_sort (@edge_below R) (outgoing e))).
  by rewrite oeq inE eqxx.
rewrite -[X in is_true X]/(sorted _ (g1 :: gs)) -oeq tmp //.
by apply/allP=> x xin /=; apply/orP; right; exact: xin.
Qed.

Definition any_edge (b : bool) (c : cell) : edge :=
  if b then low c else high c.

Lemma fc_lc_right_pt s ev events :
  close_alive_edges s events ->
  inside_box (point ev) ->
  all (fun x => lexPtEv  ev x) events ->
  {in s, forall c b, lexPt (point ev) (right_pt (any_edge b c))}.
Proof.
move=> /allP clae inbox_e /allP lexev c cin b.
have : end_edge (any_edge b c) events.
  by have := clae _ cin; rewrite /end_edge /any_edge; case: b=> /= /andP[].
move=> /orP[ | ].
  move: inbox_e => /andP[] _ /andP[]/andP[] _ botP /andP[] _ topP.
  by rewrite !inE => /orP[]/eqP ->; rewrite /lexPt ?botP ?topP.
by move=>/hasP[ev' ev'in /eqP ->]; apply: lexev.
Qed.

Lemma seq_low_high_shift s :
  s != nil ->  adjacent_cells s ->
  rcons [seq low i | i <- s] (high (last dummy_cell s)) =
  (low (head dummy_cell s) :: [seq high i | i <- s]).
Proof.
elim: s => [ // | c s +] _ /=.
  case: s => [// | c' s].
rewrite /=; move=> /(_ isT) Ih => /andP[] /eqP -> adj; congr (_ :: _).
by apply: Ih.
Qed.

Lemma cell_edges_high s :
  s != [::] -> adjacent_cells s ->
  cell_edges s =i low (head dummy_cell s) :: [seq high i | i <- s].
Proof.
move=> sn0 adj g; rewrite mem_cat; apply/idP/idP.
  move=>/orP[].
    by rewrite -(seq_low_high_shift sn0 adj) mem_rcons inE orbC => ->.
  by rewrite inE orbC => ->.
rewrite inE => /orP[/eqP -> | ].
  by rewrite map_f // head_in_not_nil.
by move=> ->; rewrite orbT.
Qed.

Lemma pvert_y_bottom p : inside_box p -> pvert_y p bottom < p_y p.
Proof.
have tmp : bottom \in [:: bottom; top] by rewrite inE eqxx.
move=> /[dup]/inside_box_valid_bottom_top=> /(_ _ tmp) val. 
move=> /andP[] /andP[] + _ _.
by rewrite (under_pvert_y val) -ltNge.
Qed.

Lemma adjacent_right_form_sorted_le_y s p :
    seq_valid s p ->
    adjacent_cells s ->
    s_right_form s ->
    sorted <=%R [seq pvert_y p (high c) | c <- s].
Proof.
elim: s => [ // | a s Ih] /=.
move=> /andP[] _ vs /[dup]/adjacent_cons adj + /andP[] _ rfs.
case s_eq : s => [ // | b s'] /= /andP[]/eqP hl _.
rewrite hl.
have bin : b \in s by rewrite s_eq inE eqxx.
have rfb := (allP rfs b bin).
have := (allP vs b bin)=> /andP[] vl vh.
have := order_below_viz_vertical vl vh.
rewrite (pvertE vl) (pvertE vh) => /(_ _ _ erefl erefl rfb) /= => -> /=.
by move: Ih; rewrite s_eq; apply; rewrite -s_eq.
Qed.

Definition edge_side_prop ev g :=
        if valid_edge g (point ev) then
          if pvert_y (point ev) g < p_y (point ev) then
             p_x (point ev) < p_x (right_pt g)
          else
             if p_y (point ev) < pvert_y (point ev) g then
             p_x (left_pt g) < p_x (point ev)
             else
           true
        else
          true.

Definition edge_side (evs : seq event) (open : seq cell) :=
  if evs is ev :: _ then
    all (edge_side_prop ev) [seq high c | c <- open]
  else true.

Definition extra_bot := Bcell nil nil bottom bottom.

Lemma last_first_cells_high open p fc cc lc le he :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  open_cells_decomposition open p = (fc, cc, lc, le, he) ->
  last bottom [seq high i | i <- fc] = le.
Proof.
move=> cbtom adj inbox_p oe.
have ctn := exists_cell cbtom adj inbox_p.
have ocd := decomposition_preserve_cells oe.
have [/eqP loc [hic ccn0]] := l_h_c_decomposition oe ctn.
have ccdec : cc = [:: head dummy_cell cc] ++ behead cc by case: (cc) ccn0.
have adje : adjacent_cells (extra_bot :: open).
  move: cbtom=> /andP[] /andP[] + + _.
  by move: adj; case: (open) => [ | c s]//= -> _ /eqP ->; rewrite eqxx.
move: adje; rewrite /= -[bottom]/(high extra_bot) ocd.
rewrite ccdec -catA cat_path /= => /andP[] _.
by rewrite loc -[bottom]/(high extra_bot) last_map=> /andP[] /eqP.
Qed.

Lemma head_last_cells_low open p fc cc lc le he :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  open_cells_decomposition open p = (fc, cc, lc, le, he) ->
  head top [seq low i | i <- lc] = he.
Proof.
move=> cbtom adj inbox_p oe.
have ctn := exists_cell cbtom adj inbox_p.
have ocd := decomposition_preserve_cells oe.
have [loc [/eqP hic ccn0]] := l_h_c_decomposition oe ctn.
have [cc'  ccdec] : exists cc', cc = rcons cc' (last dummy_cell cc).
  by elim/last_ind: (cc) ccn0 => [// | v *]; rewrite last_rcons; exists v.
have adje : adjacent_cells (extra_bot :: open).
  move: cbtom=> /andP[] /andP[] + + _.
  by move: adj; case: (open) => [ | c s]//= -> _ /eqP ->; rewrite eqxx.
move: adje; rewrite  ocd.
move: cbtom=>/andP[] /andP[] _ _.
rewrite ocd ccdec; case: (lc) => [ | flc lc' _].
  by rewrite cats0 last_cat last_rcons /= hic eq_sym => /eqP.
rewrite /= 2!cat_path last_rcons /= eq_sym => /andP[] _ /andP[] _ /andP[] + _.
by rewrite hic=> /eqP.
Qed.

Lemma high_in_first_cells_below open p first_cells cc last_cells le he :
  open_cells_decomposition open p =
  (first_cells, cc, last_cells, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  seq_valid open p ->
  s_right_form open ->
  {in cell_edges open &, no_crossing R} ->
  {in [seq high i | i <- first_cells], forall g, p_x p < p_x (right_pt g)} ->
  {in [seq high c | c <- first_cells], forall g, g <| le}.
Proof.
move=> oe cbtom adj inbox_e sval rfo noc side_cond.
have ocd := decomposition_preserve_cells oe.
have vfc : {in [seq high i | i <- first_cells], forall g, valid_edge g p}.
  move=> g /mapP[c cin geq]; have := (allP sval c).
  by rewrite ocd !mem_cat cin geq => /(_ isT) => /andP[].
move=> g /mapP[c cin geq].
have [fc1 [fc2 fceq]] : exists fc1 fc2, first_cells = fc1 ++ c :: fc2.
    by move: cin => /splitPr[ x y]; exists x, y.  
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

(* To be added to math-comp. *)
Lemma sorted_catW (T : Type) (r : rel T) s s' :
 (sorted r (s ++ s')) -> sorted r s && sorted r s'.
Proof.
case: s => [// | a s] /=.
by rewrite cat_path => /andP[] ->; apply: path_sorted.
Qed.

Lemma all_edges_opening_cells_above_first e open fc cc lc le he outg:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  s_right_form open ->
  seq_valid open (point e) ->
  inside_box (point e) ->
  {in cell_edges open ++ outg, forall g, inside_box (left_pt g)} ->
  {in cell_edges fc, forall g, p_x (point e) < p_x (right_pt g)} ->
  {in cell_edges open ++ outg &, no_crossing R} ->
  {in outg, forall g, left_pt g == (point e)} ->
  {in cell_edges fc &
      [seq high i | i <- (opening_cells_aux (point e) outg le he)],
      forall g1 g2, (g1 <| g2) && ~~ (g2 <| g1)}.
Proof.
move=> oe cbtom adj rfo sval inbox_e lefts rightslt noc outs g1 g2.
have ocd := decomposition_preserve_cells oe.
have adjf : adjacent_cells fc by move: adj; rewrite ocd => /adjacent_catW [].
have [/eqP -> | fcn0]:= (boolP (fc == [::])) => //.
have := l_h_in_open cbtom adj inbox_e; rewrite oe /=.
move => -[cle [che [clein [chein [loeq hieq]]]]].
have hdfc : low (head dummy_cell fc) = bottom.
  move: cbtom=> /andP[] /andP[] _; rewrite ocd => /eqP.
  by  move: fcn0; case: (fc).
have bin : bottom \in [:: bottom; top] by rewrite inE eqxx.
have noc' : {in cell_edges open &, no_crossing R}.
  by move: noc; apply: sub_in2=> g gin; rewrite mem_cat gin.
rewrite (cell_edges_high fcn0 adjf) inE => /orP[/eqP -> | ].
  rewrite hdfc=> gin0.
  have gin : g2 \in outg ++ [:: he].
      move: gin0=>/mapP[c /opening_cells_aux_subset /andP[] _ hiin geq].
      by rewrite cats1 mem_rcons geq.
  have g2in : g2 \in cell_edges open ++ outg.
    move: gin; rewrite !mem_cat => /orP[-> | ]; rewrite ?orbT //.
    by rewrite !inE => /eqP ->; rewrite -?loeq -?hieq ?map_f ?orbT.
  have : below_alt bottom g2.
    apply: noc=> //; rewrite ocd; move: fcn0 hdfc.
    by case: (fc) => [ | ? ?] //= _ <-; rewrite inE eqxx.
  have := pvert_y_bottom (lefts _ g2in); rewrite ltNge => /negbTE clbot.
  have := (lefts _ g2in) => /inside_box_valid_bottom_top/(_ bin)=> vl2.
  have g2lab : left_pt g2 >>> bottom by move: (lefts _ g2in) => /andP[]/andP[].
  suff : ~~(g2 <| bottom) by rewrite /below_alt => /negbTE -> [-> | //].
  apply/negP=> absglow.
  have : (left_pt g2 == left_pt g2) || (right_pt g2 == left_pt g2).
    by rewrite eqxx.
  move=>/valid_edge_extremities vlg2.
  have := order_below_viz_vertical vlg2 vl2.
  move: (pvertE vl2) => /[dup] /intersection_on_edge /= []A1 A2 ->.
  move: (pvertE vlg2) =>
           /[dup] /intersection_on_edge /= [] B1 /esym/eqP B2 ->.
  move=> /(_ _ _ erefl erefl) /= /(_ absglow).
  by move: (on_pvert (left_on_edge g2)) => /= ->; rewrite clbot.
move=> g1fc.
move: (g1fc) => /mapP[c1 c1in g1eq].
have c1in' : c1 \in open by rewrite ocd mem_cat c1in.
have v1 : valid_edge g1 (point e).
  by have := (allP sval c1 c1in') => /andP[]; rewrite g1eq.
have [vle vhe] : valid_edge le (point e) /\ valid_edge he (point e).
  by have [] := l_h_valid cbtom adj inbox_e sval oe.
have v2' : {in outg, forall g, valid_edge g (point e)}.
  move=> g gin; have /eqP <- : left_pt g == point e by apply: outs.
  by move: (@valid_edge_extremities R g (left_pt g)); rewrite eqxx; apply.
move=> /mapP[c2 /opening_cells_aux_subset /andP[] _ g2in g2eq ].
have v2 : valid_edge g2 (point e).
  by move: g2in; rewrite inE g2eq => /orP[/eqP -> // | /v2'].
have vg1levle : pvert_y (point e) g1 <= pvert_y (point e) le.
  have rightslt' : {in [seq high i | i <- fc],
         forall g, p_x (point e) < p_x (right_pt g)}.
    by move: rightslt; apply: sub_in1=> g gin; rewrite mem_cat gin orbT.
  have := high_in_first_cells_below oe cbtom adj inbox_e sval rfo noc'.
  move=> /(_ rightslt' _ g1fc) => g1le.
(* TODO : from here to end of subproof: make it a lemma. *)
  set p1 := (Bpt (p_x (point e)) (pvert_y (point e) g1)).
  have /eqP p1x : p_x p1 = p_x (point e) by [].
  have p1on : p1 === g1 by rewrite pvert_on.
  have [v1' vl1] : valid_edge g1 p1 /\ valid_edge le p1.
    by split; rewrite (same_x_valid _ p1x).
  have := order_edges_viz_point' v1' vl1 g1le.
  rewrite (under_onVstrict v1') p1on => /(_ isT).
  by rewrite under_pvert_y.
suff : ~~ (g2 <| g1).
  have : below_alt g1 g2.
    apply: noc; rewrite mem_cat.
      by rewrite mem_cat g1eq map_f // orbT.
    move: g2in; rewrite inE g2eq=> /orP[/eqP -> | ].
      by rewrite mem_cat -hieq map_f // orbT.
    move=> ->; by rewrite orbT.
  by move=>[-> ->// | -> //].
suff vleltvg2 : pvert_y (point e) le < pvert_y (point e) g2.
  apply/negP=> abslow.
  have := order_below_viz_vertical v2 v1.
  move: (pvertE v2) => /[dup] /intersection_on_edge /= [] A1 A2 ->.
  move: (pvertE v1) =>
         /[dup] /intersection_on_edge /= [] B1 /esym/eqP B2 ->.
  move=> /(_ _ _ erefl erefl) /= /(_ abslow).
  by rewrite leNgt (le_lt_trans vg1levle vleltvg2).
have [egtle elthe]:= l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have lelte: pvert_y (point e) le < p_y (point e).
  by move: egtle; rewrite (under_pvert_y vle) // -ltNge.
have eleg2 : p_y (point e) <= pvert_y (point e) g2.
  rewrite -(under_pvert_y v2).
  move: g2in; rewrite g2eq inE => /orP[ /eqP -> | /outs /eqP <-].
    by rewrite (under_onVstrict vhe) elthe orbT.
  by rewrite left_pt_below.
by apply: lt_le_trans eleg2.
Qed.

(* Temporary trial, but this lemma might be better placed in
  points_and_edges. *)
Lemma decomposition_above_high_fc e open fc cc lc le he c1:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  s_right_form open ->
  seq_valid open (point e) ->
  c1 \in fc -> point e >>> high c1.
Proof.
move=> oe cbtom adj  inbox_e rfo sval c1in.
have ocd := decomposition_preserve_cells oe.
rewrite under_pvert_y; last first.
    by apply: (proj2 (andP (allP sval c1 _))); rewrite ocd !mem_cat c1in.
rewrite -ltNge.
have pale : pvert_y (point e) le < p_y (point e).
  have [+ _] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  rewrite under_pvert_y; last first.
    by have [] := l_h_valid cbtom adj inbox_e sval oe.
  by rewrite -ltNge.
apply: le_lt_trans pale.
move: c1in.
have [fceq | [fc' [lfc fceq]]] : fc = nil \/ exists fc' lfc, fc = rcons fc' lfc.
    by elim/last_ind : (fc) => [ | fc' lfc _];[left | right; exists fc', lfc].
  by rewrite fceq.
have := last_first_cells_high cbtom adj inbox_e oe.
rewrite fceq map_rcons last_rcons => <-.
rewrite mem_rcons inE => /orP[/eqP c1lfc | c1o]; first  by rewrite c1lfc.
move: c1o fceq=>/splitPr[a b]; rewrite -cats1 -catA /= => fceq.
(* requirement for path_edge_below_pvert_y *)
have req1 : all (valid_edge (R := _) ^~ (point e))
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
have : path (<=%R) (pvert_y (point e) (high c1))
  [seq pvert_y (point e) (high i) | i <- b ++ [:: lfc]].
  by have := path_edge_below_pvert_y req1 req2; rewrite -map_comp.
rewrite le_path_sortedE => /andP[] /allP + _.
move=> /(_ (pvert_y (point e) (high lfc))); apply.
by apply/mapP; exists lfc => //=; rewrite mem_cat inE eqxx orbT.
Qed.

Lemma decomposition_under_low_lc e open fc cc lc le he c1:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  s_right_form open ->
  seq_valid open (point e) ->
  c1 \in lc -> point e <<< low c1.
Proof.
move=> oe cbtom adj  inbox_e rfo sval c1in.
have ocd := decomposition_preserve_cells oe.
rewrite strict_under_pvert_y; last first.
    by apply: (proj1 (andP (allP sval c1 _))); rewrite ocd !mem_cat c1in ?orbT.
have puhe : p_y (point e) < pvert_y (point e) he.
  have [ _ ] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  rewrite strict_under_pvert_y //.
 by have [] := l_h_valid cbtom adj inbox_e sval oe.
apply: (lt_le_trans puhe).
move: c1in; case lceq : lc => [ // | flc lc'] c1in.
have := head_last_cells_low cbtom adj inbox_e oe.
rewrite lceq /= => <-.
move: c1in; rewrite inE => /orP[/eqP c1flc | c1o]; first by rewrite c1flc.
move: c1o lceq=> /splitPr[a b]=> lceq.
(* requirement for path_edge_below_pvert_y *)
have req1 : all (@valid_edge R ^~ (point e)) [seq low i | i <- flc :: a ++ c1 :: b].
  apply/allP; apply: (sub_in1 _ (seq_valid_low sval)); apply: sub_map.
  rewrite ocd lceq=> x; rewrite 2!mem_cat => ->.
  by rewrite !orbT.
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
  by rewrite ocd lceq 2!map_cat 2!cat_path => /andP[]  _ /andP[] _ /= /andP[] _.
have : path (<=%R) (pvert_y (point e) (low flc))
  [seq pvert_y (point e) (low i) | i <- a ++ c1 :: b].
  by have := path_edge_below_pvert_y req1 req2; rewrite -map_comp.
rewrite le_path_sortedE => /andP[] /allP + _.
move=> /(_ (pvert_y (point e) (low c1))); apply.
by apply/mapP; exists c1 => //=; rewrite !(mem_cat, inE, eqxx, orbT).
Qed.

Lemma in_new_cell_not_in_first_old e open fc cc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  s_right_form open ->
  seq_valid open (point e) ->
  out_left_event e ->
  {in cell_edges open ++ outgoing e &, no_crossing R} ->
  all open_cell_side_limit_ok open ->
  {in [seq high c | c <- fc], forall g, p_x (point e) < p_x (right_pt g)} ->
  {in fc & opening_cells (point e) (outgoing e) le he,
     forall c1 c2, o_disjoint c1 c2}.
Proof.
move=> oe cbtom adj  inbox_e rfo sval outs noc lok redges.
have ocd := decomposition_preserve_cells oe.
set result_open :=
   fc ++ opening_cells (point e) (outgoing e) le he ++ lc.
have steq : step e open nil = (result_open, closing_cells (point e) cc).
   by rewrite /step oe.
have adj' : adjacent_cells result_open.
  by have := step_keeps_adjacent inbox_e outs sval cbtom steq adj.
rewrite /opening_cells.
set new_cells := opening_cells_aux _ _ _ _.
have := l_h_in_open cbtom adj inbox_e=> -[cle [che [clein [chein ]]]].
rewrite oe /= => -[leeq heeq].
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have [/eqP ole [/eqP ohe ccn0]]:=
   l_h_c_decomposition oe (exists_cell cbtom adj inbox_e).
have nceq : opening_cells (point e) (outgoing e) le he = new_cells by [].
have [nle [nhe _]]:=
    higher_lower_equality outs oe nceq (exists_cell cbtom adj inbox_e)
         vle vhe.
have := open_not_nil (sort (@edge_below R) (outgoing e)) vle vhe.
rewrite -/new_cells => ncn0.
have [fceq | [fc' [lfc fceq]]] : fc = nil \/ exists fc' lfc, fc = rcons fc' lfc.
    by elim/last_ind : (fc) => [ | fc' lfc _];[left | right; exists fc', lfc].
  by rewrite fceq.
have lfceq : high lfc = le.
  case fc'eq : fc' => [ | init fc''].
    move: adj; rewrite ocd fceq fc'eq => /=.
    by move: ccn0 ole; case: (cc) => [ | b cc'] //= _ -> /andP[]/eqP ->.
  move: adj; rewrite ocd fceq fc'eq /= cat_path=> /andP[] _.
  rewrite last_rcons.
  by move: ccn0 ole; case: (cc) => [ | b cc'] //= _ -> /andP[]/eqP ->.
set s1 := [seq high c | c <- fc'].
set s2 := [seq high c | c <- behead new_cells ++ lc].
set g2 := high (head dummy_cell new_cells).
have roeq : [seq high c | c <- result_open] = s1 ++ [:: le, g2 & s2].
  rewrite /result_open /opening_cells map_cat fceq -cats1 map_cat -catA /=.
  congr (_ ++ (_ :: _)) => //.
  rewrite /g2 /s2 2!map_cat -/new_cells.
  by move: ncn0; case: (new_cells).
have val' : all (fun g => @valid_edge R g (point e)) (s1 ++ [:: le, g2 & s2]).
  apply/allP=> g; rewrite mem_cat=> /orP[/mapP[c cin ->] | innc].
    apply: (proj2 (andP (allP sval c _))); rewrite ocd fceq mem_cat mem_rcons.
    by rewrite inE cin orbT.
  move: innc; rewrite inE=> /orP[/eqP -> // | gnew].
    have [c cin ->] : exists2 c, c \in new_cells ++ lc & g = high c.
      move: gnew; rewrite inE => /orP[gg2 | gs2].
      exists (head dummy_cell new_cells);[ | by rewrite (eqP gg2)].
      by rewrite mem_cat head_in_not_nil.
    move: gs2; rewrite /s2 map_cat mem_cat => /orP[].
      move=> /mapP[c /behead_subset cin ->]; exists c=> //.
      by rewrite mem_cat cin.
    by move=> /mapP[c cin ->]; exists c=> //; rewrite mem_cat cin orbT.
  move: cin; rewrite mem_cat=> /orP[] cin; last first.
    by have:= allP sval c; rewrite ocd !mem_cat cin !orbT => /(_ isT)/andP[].
  move: cin=>/opening_cells_aux_subset=>/andP[] _.
  rewrite /= inE mem_sort=> /orP[/eqP -> //| /outs it].
  by apply: valid_edge_extremities; rewrite it.
have rfr' : sorted (@edge_below R) (s1 ++ [:: le, g2 & s2]).
  have rfr := step_keeps_right_form cbtom adj inbox_e sval noc outs rfo steq.
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
have [lu ha] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have p'under : p' <<< g2.
  have : head dummy_cell new_cells \in new_cells by rewrite head_in_not_nil.
  move=>/opening_cells_aux_subset=> /andP[] _; rewrite -/g2 => g2in.
  rewrite (strict_under_pvert_y vg2').
  rewrite -(eqP (same_pvert_y vg2 samex)).
  apply: (lt_le_trans (_ : p_y p' < p_y (point e))).
    by rewrite [X in X < _]/= ltNge -(under_pvert_y vle).
  move: g2in; rewrite inE=> /orP[/eqP -> | ].
    by apply: ltW; rewrite -(strict_under_pvert_y vhe).
  rewrite mem_sort=>/outs/eqP lg2e.
  by rewrite -(under_pvert_y vg2) -lg2e left_pt_below.
have val'' : all (fun g => valid_edge g p') (s1 ++ [:: le, g2 & s2]).
  by apply/allP=> g gin; rewrite -(same_x_valid _ samex); apply: (allP val').
have strict_above:= edges_partition_strictly_above val'' rfr' p'above p'under.
move=> c1 c2 c1in c2in p; apply/negP=> /andP[]/andP[] /andP[]belhc1 _ c1l.
move=>/andP[] /andP[] _ ablc2 c2l.
have c1ok : open_cell_side_limit_ok c1.
  by apply: (allP lok); rewrite ocd !mem_cat c1in.
have leop : le \in cell_edges open by rewrite -leeq mem_cat map_f.
have heop : he \in cell_edges open by rewrite -heeq mem_cat map_f ?orbT.
have lectxt : le \in cell_edges open ++ outgoing e by rewrite mem_cat leop.
have hectxt : he \in cell_edges open ++ outgoing e by rewrite mem_cat heop.
have lebhe : le <| he.
  have [// | abs ] : below_alt le he by apply: noc.
  by move: lu; have := order_edges_viz_point' vhe vle abs (underW ha)=> ->.
have outs':
   {in sort (@edge_below R) (outgoing e), forall g, left_pt g == (point e)}.
 by move: outs; apply: sub_in1=> g; rewrite mem_sort.
have c2ok : open_cell_side_limit_ok c2.
  have noco : {in [:: le, he & outgoing e] &, no_crossing R}.
    move: noc; apply: sub_in2=> g; rewrite !inE.
    move=> /orP[/eqP -> // | /orP[/eqP -> // | gino]].
    by rewrite mem_cat gino orbT.
  have := opening_cells_side_limit vle vhe lebhe (underWC lu) ha noco outs.
  by move=> /allP/(_ c2 c2in).
move: (c1l) (c2l) => /valid_high_limits => /(_ c1ok) vc1. 
move=>/valid_low_limits =>/(_ c2ok) vc2.
have highc1in : high c1 \in rcons s1 le.
  move: c1in; rewrite fceq !mem_rcons !inE => /orP[/eqP -> | ].
    by rewrite lfceq eqxx.
  by move=> ?; rewrite map_f ?orbT.
have lowc2in : low c2 = le \/ low c2 \in [seq high i | i <- new_cells].
  have := opening_cells_seq_edge_shift outs' vle vhe.
  set tmp := rcons _ _.
  have /[swap] <- : low c2 \in tmp by rewrite mem_rcons inE map_f ?orbT.
  by rewrite inE -/new_cells=> /orP[/eqP -> // |];[left | right].
case: lowc2in=> [lowc2le | lowc2hnc].
  move: (belhc1); rewrite strict_under_pvert_y // => belhc1'.
  move: ablc2; rewrite under_pvert_y // lowc2le; case/negP.
  have [/eqP c1lfc | c1nlfc] := boolP(c1 == lfc).
    by apply/ltW/(lt_le_trans belhc1'); rewrite c1lfc lfceq lexx.
  have c1fc' : c1 \in fc'.
    by move: c1in; rewrite fceq mem_rcons inE (negbTE c1nlfc).
  have : high c1 <| le.
    have noc' : {in cell_edges open &, no_crossing R}.
    by move: noc; apply: sub_in2=> g gin; rewrite mem_cat gin.
    have := high_in_first_cells_below oe cbtom adj inbox_e sval rfo noc' redges.
    by apply; apply: map_f.
  move/edge_below_pvert_y=>/(_ _ vc1); rewrite -lowc2le vc2=> /(_ isT) c1c2.
  by apply/ltW/(lt_le_trans belhc1').
move: (strict_above (high c1) (low c2)).
rewrite -lfceq /s1 -map_rcons -fceq map_f //.
have -> : g2 :: s2 = [seq high c | c <- new_cells ++ lc].
  by move: ncn0; rewrite /g2 /s2; case : (new_cells).
rewrite map_cat mem_cat lowc2hnc => /(_ isT isT); case/negP.
apply: (edge_below_from_point_above _ vc2 vc1) => //; last first.
  by rewrite (strict_nonAunder vc2) negb_and ablc2 ?orbT.
apply: noc.
  rewrite mem_cat.
  have := opening_cells_aux_subset c2in=> /andP[].
  by rewrite inE mem_sort => /orP[/eqP -> | -> ]; rewrite ?leop ?orbT.
rewrite !mem_cat map_f ?orbT //.
by rewrite ocd mem_cat c1in.
Qed.

(*
Definition lex_edges (s : seq edge) (p : pt) :=
  all (fun g => lexPt (left_pt g) p) s.

Definition lex_cell_edges_evs (s : seq cell) (evs : seq event) :=
  all (fun ev => lex_edges (cell_edges s) (point ev)) evs.

Lemma step_keeps_lex_cell_edges ev future open fc cc lc le he :
  path lexPtEv ev future ->
  lex_cell_edges_evs 


Lemma open_cells_decomposition_last_right e open fc cc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  adjacent_cells open ->
  close_alive_edges open ->
  {in cell_edges lc, forall g, p_x (point e) < p_x (right_pt g)}.
*)

Lemma pred_of_seq_mem {T : eqType} (s : seq T) (x : T) :
  (@pred_of_seq _ s x) = (x \in s).
Proof.
by [].
Qed.

Lemma in_new_cell_not_in_last_old e open fc cc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  s_right_form open ->
  seq_valid open (point e) ->
  out_left_event e ->
  {in cell_edges open ++ outgoing e &, no_crossing R} ->
  all (edge_side_prop e) [seq high c | c <- open] ->
  all open_cell_side_limit_ok open ->
(*  {in [seq high c | c <- lc], forall g, p_x (left_pt g) < p_x (point e)} -> *)
  {in opening_cells (point e) (outgoing e) le he & lc,
     forall c1 c2, o_disjoint c1 c2}.
Proof.
move=> oe cbtom adj inbox_e rfo sval outs noc aesp lok (* ledges *).
have ocd := decomposition_preserve_cells oe.
set new_cells := opening_cells _ _ _ _.
set result_open := fc ++ new_cells ++ lc.
have steq : step e open nil = (result_open, closing_cells (point e) cc).
   by rewrite /step oe.
have adj' : adjacent_cells result_open.
  by have := step_keeps_adjacent inbox_e outs sval cbtom steq adj.
have := l_h_in_open cbtom adj inbox_e=> -[cle [che [clein [chein ]]]].
rewrite oe /= => -[leeq heeq].
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have [/eqP ole [/eqP ohe ccn0]]:=
   l_h_c_decomposition oe (exists_cell cbtom adj inbox_e).
have [nle [nhe _]]:=
    higher_lower_equality outs oe erefl (exists_cell cbtom adj inbox_e)
         vle vhe.
have := open_not_nil (sort (@edge_below R) (outgoing e)) vle vhe.
rewrite -[X in X != [::]]/new_cells => ncn0.
move=> c1 c2 c1in c2in.
 have [s3 [s4 lceq]] : exists s3 s4, lc = s3 ++ c2 :: s4.
  by move:c2in=> /splitPr[s1 s2]; exists s1, s2.
have lceq' : lc = rcons s3 c2 ++ s4 by rewrite -cats1 -catA.
have [s1 [s2 nceq']] : exists s1 s2, new_cells = s1 ++ c1 :: s2.
  by move:c1in=> /splitPr[s1 s2]; exists s1, s2.
have hs2 : high (last c1 s2) = he.
  by move: nhe; rewrite ohe -/new_cells nceq' last_cat /=.
have lt1 : p_y (point e) < pvert_y (point e) he.
  have [_ ]:= l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  by rewrite strict_under_pvert_y.
have lc2q : last he [seq high i | i <- s3] = low c2.
  move: adj' => /adjacent_catW [] _; rewrite nceq' -catA => /adjacent_catW[] d.
  rewrite /= cat_path lceq cat_path=>/andP[] _ /andP[] _ /=.
  move=> /andP[] /eqP <- _; case: (s3) => [ // | a s'] /=.
  by rewrite last_map.
have rf' : s_right_form (last  c1 s2 :: rcons s3 c2).
(* TODO: make this one shorter. *)
  apply/allP=> c; rewrite inE=> /orP[/eqP -> {c}| cin].
    have := step_keeps_right_form cbtom adj inbox_e sval noc outs rfo.
    move=> /(_ nil result_open
             (closing_cells (point e)
       (open_cells_decomposition open (point e)).1.1.1.2)).
    rewrite /step oe; rewrite /= => /(_ erefl)/allP; apply.
    suff : {subset c1 :: s2 <= result_open} by apply; rewrite mem_last.
    move=> c cin; rewrite /result_open mem_cat orbC mem_cat nceq'.
    by rewrite mem_cat cin orbT.
  by apply: (allP rfo); rewrite ocd lceq' !mem_cat cin ?orbT.
have le2 : path <=%R (pvert_y (point e) he)
   [seq pvert_y (point e) (high i) | i <- rcons s3 c2].
  move: adj' => /adjacent_catW [] _; rewrite nceq' -catA => /adjacent_catW[] _.
  rewrite /= cat_path lceq' => /andP[] _.
  rewrite -[X in is_true X -> _]/
       (adjacent_cells ((last c1 s2 :: rcons s3 c2) ++ s4)).
  move=>/adjacent_catW[]/seq_edge_below'/(_ rf') /= => /andP[] _ + _.
  move/path_edge_below_pvert_y; rewrite hs2.
  move=> /(_ (point e)); rewrite -map_comp; apply.
  rewrite /= vhe; apply/allP=> g /mapP [c cin ->].
  apply: (proj2 (andP (allP sval c _))).
  by rewrite ocd lceq' !mem_cat cin !orbT.
have lein : le \in cell_edges open ++ outgoing e.
  rewrite 2!mem_cat; apply/orP/or_introl/orP/or_introl; apply/mapP.
  by exists cle.
have hein : he \in cell_edges open ++ outgoing e.
  rewrite 2!mem_cat; apply/orP/or_introl/orP/or_intror; apply/mapP.
  by exists che.

have c1c2 : high c1 <| low c2.
  have /andP[_] := opening_cells_subset c1in.
  rewrite inE=> /orP[hc1he | hc1o].
  (* use that sorted edge_below lc, plus transitivity in this subset. *)
    have treblc : {in he :: [seq high i | i <- lc] & &,
                  transitive (@edge_below R)}.
      elim/last_ind : {-1} (cc) (erefl cc) ccn0 => [// | cc' ccl' _ cceq _].
(* This should be a general hypothesis of the lemma, established as an
   invariant. *)
    have all_left :{in he :: [seq high i | i <- lc], forall g,
           p_x (left_pt g) < p_x (point e)}.
      have lelow := decomposition_under_low_lc oe cbtom adj inbox_e rfo sval.
      have ccl'he : high ccl' = he by move: ohe; rewrite cceq last_rcons.
      have adjlc' : adjacent_cells (ccl' :: lc).
        move: adj; rewrite ocd cceq -cats1 -!catA /= => /adjacent_catW[] _.
        by move=> /adjacent_catW[] _ /=.
      have := seq_low_high_shift => /(_ (ccl' :: lc) isT adjlc') /= => - [] tmp.   move=> g; rewrite inE => /orP[/eqP -> | ].
    have ccl'o : ccl' \in open.
      by rewrite ocd cceq !(mem_cat, mem_rcons, inE) eqxx orbT.
    have := allP aesp (high ccl') (map_f _ ccl'o); rewrite /edge_side_prop.
    by rewrite ccl'he vhe ltNge le_eqVlt orbC lt1 /=.
    move: tmp; set s5 := rcons _ _ => tmp gin.
    have : g \in s5 by rewrite tmp inE gin orbT.
    rewrite /s5 mem_rcons inE orbC=> /orP[/mapP[c' c'in gc'] | ].
    have vc' : valid_edge (low c') (point e).
     apply: (proj1 (andP (allP sval c' _))).
     by rewrite ocd !mem_cat c'in !orbT.
     have := lelow _ c'in; rewrite strict_under_pvert_y // => ga.
     move: gin=> /mapP[c'' c''in gc''].
     have c''o : c'' \in open by rewrite ocd !mem_cat c''in !orbT.
     have := allP aesp (high c'') (map_f _ c''o); rewrite /edge_side_prop.
       rewrite (proj2 (andP (allP sval _ c''o))).
       by rewrite -gc'' gc' ltNge le_eqVlt ga orbT /=.
    move: cbtom=> /andP[] _; rewrite ocd cceq -cats1 /= !last_cat /= => /eqP ->.
move=> /eqP ->.
  by move: inbox_e=> /andP[] _ /andP[] _ /andP[] + _.
(* finished proving all_left *)
have noc' : {in he :: [seq high i | i <- lc] &, no_crossing R}.
 apply: sub_in2 noc.
  move=> g; rewrite inE => /orP[/eqP -> // | gin].
  by rewrite ocd !(mem_cat, map_cat) gin !orbT.
  have sval' : {in he :: [seq high i | i <- lc], forall g, valid_edge g (point e)}.
  move=> g; rewrite inE=> /orP[/eqP ->// | /mapP[c' c'in gc']].
  by rewrite gc'; apply: (proj2 (andP (allP sval c' _))); rewrite ocd !mem_cat c'in !orbT.
  by have := edge_below_trans (or_intror all_left) sval' noc'.

    have adj2 : adjacent_cells (last c1 s2 :: rcons s3 c2).
      move: adj'; rewrite /result_open => /adjacent_catW[] _.
      rewrite nceq' -catA /= => /adjacent_catW[] _.
      by rewrite /= cat_path lceq' cat_path => /andP[] _ /andP[] +.
      have := seq_edge_below' adj2 rf' => /= /andP[] _.
      rewrite (path_sorted_inE treblc); last first.
      apply/allP=> g; rewrite hs2 !inE => /orP[/eqP -> | ].
      by rewrite pred_of_seq_mem inE eqxx.
rewrite pred_of_seq_mem inE lceq' map_cat mem_cat=> ->.
by rewrite orbT.
move=> /andP[] + _ => /allP allofthem. 
have [s3nil | s3nnil] := boolP (s3 == nil).
  by rewrite (eqP hc1he) -lc2q (eqP s3nil) edge_below_refl.
move: (allofthem (last he [seq high i | i <- s3])).
   case: (s3) s3nnil lc2q => [ // | a tl] /= _; rewrite map_rcons -cats1.
   rewrite -/((_ :: _) ++ _) mem_cat mem_last=> lc2q /(_ isT).
   by rewrite lc2q hs2 (eqP hc1he).

  have : below_alt (high c1) (low c2).
    apply: noc; rewrite mem_cat; first by rewrite hc1o orbT.
    by rewrite ocd !(cell_edges_cat, mem_cat) (map_f _ c2in) !orbT.
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
  have sval' := opening_valid outs vle vhe.
  rewrite (proj2 (andP (allP sval' c1 _))) //.
  rewrite (proj1 (andP (allP sval c2 _))); last first.
    by rewrite ocd !mem_cat c2in ?orbT.
  by rewrite abs => /(_ isT isT).
move=> p; apply/negP=> /andP[] sio1 sio2.
have lho_sub : {subset le :: he :: outgoing e <= cell_edges open ++ outgoing e}.
  move=> g; rewrite !inE =>/orP[/eqP -> // | /orP[/eqP -> // | ]].
  by rewrite mem_cat orbC => -> .
have noc' : {in le :: he :: outgoing e &, no_crossing R}.
  by apply: (sub_in2 lho_sub). 
have [_ euh] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have [eal _] := l_h_above_under cbtom adj inbox_e sval oe.
have lebhe : le <| he.
  have altlh : below_alt le he by apply: noc'; rewrite !inE eqxx ?orbT.
  by apply: (edge_below_from_point_above altlh vle vhe).
have vp1 : valid_edge (high c1) p.
  apply: (proj2 (andP (strict_inside_open_valid  _  sio1))).
  by apply: (allP (opening_cells_side_limit vle vhe lebhe eal euh noc' outs)).
have vp2 : valid_edge (low c2) p.
  apply: (proj1 (andP (strict_inside_open_valid  _  sio2))).
  apply: (allP lok); rewrite ocd lceq'.
  by rewrite !(mem_cat, mem_rcons, inE) eqxx ?orbT.
have := edge_below_pvert_y vp1 vp2 c1c2; rewrite leNgt => /negP; apply.
have lc2p : pvert_y p (low c2) < p_y p.
  move: (sio2) => /andP[] /andP[] _ + _.
  by rewrite under_pvert_y // -ltNge.
have phc1 : p_y p < pvert_y p (high c1).
  move: (sio1) => /andP[] /andP[] + _ _.
  by rewrite strict_under_pvert_y.
by apply: lt_trans phc1.
Qed.

(*
set s1 := [seq high c | c <- fc'].
set s2 := [seq high c | c <- behead new_cells ++ lc].
set g2 := high (head dummy_cell new_cells).
have roeq : [seq high c | c <- result_open] = s1 ++ [:: le, g2 & s2].
  rewrite /result_open /opening_cells map_cat fceq -cats1 map_cat -catA /=.
  congr (_ ++ (_ :: _)) => //.
  rewrite /g2 /s2 2!map_cat -/new_cells.
  by move: ncn0; case: (new_cells).
have val' : all (fun g => @valid_edge R g (point e)) (s1 ++ [:: le, g2 & s2]).
  apply/allP=> g; rewrite mem_cat=> /orP[/mapP[c cin ->] | innc].
    apply: (proj2 (andP (allP sval c _))); rewrite ocd fceq mem_cat mem_rcons.
    by rewrite inE cin orbT.
  move: innc; rewrite inE=> /orP[/eqP -> // | gnew].
    have [c cin ->] : exists2 c, c \in new_cells ++ lc & g = high c.
      move: gnew; rewrite inE => /orP[gg2 | gs2].
      exists (head dummy_cell new_cells);[ | by rewrite (eqP gg2)].
      by rewrite mem_cat head_in_not_nil.
    move: gs2; rewrite /s2 map_cat mem_cat => /orP[].
      move=> /mapP[c /behead_subset cin ->]; exists c=> //.
      by rewrite mem_cat cin.
    by move=> /mapP[c cin ->]; exists c=> //; rewrite mem_cat cin orbT.
  move: cin; rewrite mem_cat=> /orP[] cin; last first.
    by have:= allP sval c; rewrite ocd !mem_cat cin !orbT => /(_ isT)/andP[].
  move: cin=>/opening_cells_aux_subset=>/andP[] _.
  rewrite /= inE mem_sort=> /orP[/eqP -> //| /outs it].
  by apply: valid_edge_extremities; rewrite it.
have rfr' : sorted (@edge_below R) (s1 ++ [:: le, g2 & s2]).
  have rfr := step_keeps_right_form cbtom adj inbox_e sval noc outs rfo steq.
  by have /path_sorted := seq_edge_below' adj' rfr; rewrite roeq.

*)


(*
Lemma firsts_cell_no_top_edge open p first_cells cc last_cells low_f high_f:
  open_cells_decomposition open p =
  (first_cells, cc, last_cells, low_f, high_f) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  seq_valid open p ->
  s_right_form open ->
  top \notin [seq high c | c <- first_cells].
Proof.
move=> oe cbtom adj inbox_e sval rfo.
have ocd := decomposition_preserve_cells oe.
have := l_h_above_under_strict cbtom adj inbox_e sval rfo oe => /andP[] + _.
have top2 : top \in [:: bottom; top] by rewrite !inE eqxx orbT.
have vt := inside_box_valid_bottom_top inbox_e top2.
have vl : valid_edge low_f p.
  have [c1 [c2 [c1in [_ ]]]] := l_h_in_open cbtom adj inbox_e.
  by rewrite oe /= => -[] <- _; have := allP sval c1 c1in => /andP[].
have := order_edges_viz_point' vt vl.
*)

Lemma step_keeps_edge_side ev open closed open' closed' events :
  step ev open closed = (open', closed') ->
  all inside_box [seq point i | i <- ev :: events] ->
  out_left_event ev ->
  s_right_form open ->
  cells_bottom_top open ->
  adjacent_cells open ->
  seq_valid open (point ev) ->
  close_edges_from_events (ev :: events) ->
  close_alive_edges open' events ->
  path lexPtEv ev events ->
  {in cell_edges open ++ outgoing ev &, no_crossing R} ->
  edge_side (ev :: events) open ->
  edge_side events open'.
Proof.
rewrite /step.
case oe: (open_cells_decomposition open (point ev)) => [[[[fc cc] lc] le] he].
move: events => [// | ev' events] [] <- _ {open' closed'}
  + outs rfo cbtom adj sval cle clae lexev noc /allP partedge.
rewrite [X in X -> _]/= => /andP[] inbox_e /andP[] inbox_e' inbox_o.
have [lec [hec [cc' [ocd [A [B [C D]]]]]]]:= lhc_dec cbtom adj inbox_e oe.
have noco :  {in cell_edges open &, no_crossing R}.
  by move: noc; apply: sub_in2=> g gin; rewrite mem_cat gin.
have lef c : c \in open -> p_x (left_pt (high c)) <= p_x (point ev).
  by move=> cino; have []:= andP (proj2 (andP (allP sval c cino))).
have evev' : lexPt (point ev) (point ev') by case/andP: lexev.
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have /eqP  := @higher_edge_new_cells ev le  he outs _ erefl vle vhe.
set hec' := last _ _ => E.
have hec'in : hec' \in opening_cells (point ev) (outgoing ev) le he.
   have : opening_cells (point ev) (outgoing ev) le he != nil.
     by apply: open_not_nil.
  rewrite /hec'.
  by case: (opening_cells _ _ _) => [// | /= ? ? _]; rewrite mem_last.
have rpt_ev' : forall g, 
  (g \in [:: bottom; top]) || (right_pt g == point ev') -> edge_side_prop ev' g.
  move=> g /orP[gbt | gev']; rewrite /edge_side_prop.
    move: inbox_e'=> /andP[] _ /andP[] /andP[] + + /andP[]; move: gbt.
    by rewrite !inE=> /orP[] /eqP ->; case: ifP=> //; case: ifP=> //; case: ifP.
  case: ifP => [ _ | //].
  have := on_pvert (right_on_edge g); rewrite (eqP gev') => ->.
  by rewrite !lt_irreflexive.
have commondiff c : c \in hec :: fc ++ lc -> p_x (point ev) != p_x (point ev') ->
  edge_side_prop ev' (high c).
  move=> cin diffx; rewrite /edge_side_prop.
  have cino : c \in open.    
    by move: cin; rewrite ocd !(inE, mem_cat) => /orP[/eqP -> | /orP[] ->];
    rewrite ?orbT // C D mem_last ?orbT.
  have : end_edge (high c) (ev' :: events).
    move: cin; rewrite inE => /orP[/eqP -> | cin]; last first.
      apply: (proj2 (andP (allP clae c _))).
      by move: cin; rewrite !mem_cat => /orP[] ->; rewrite ?orbT.
    move: (allP clae hec'); rewrite !mem_cat hec'in ?orbT.
    by move=> /(_ isT) /andP[]; rewrite B -E.
  rewrite /end_edge /event_close_edge /= orbA.
  move => /orP[rpt_easy | /hasP [ev2 ev2in /eqP rhc]].
    by apply: (rpt_ev' _ rpt_easy).
  case:ifP=> [vev' | //]; case:ifP=> [cbev' | _]; [ | case:ifP=> [caev' | // ]].
    rewrite rhc.
    have /orP[-> // | /andP[samex2 cmp2]] : lexPt (point ev') (point ev2).
      move: lexev; rewrite /= => /andP[] _; rewrite path_sortedE; last first.
        exact: lexPtEv_trans.
      by move=> /andP[] /allP /(_ ev2 ev2in).
    have := on_pvert (right_on_edge (high c)); rewrite rhc =>samey.
    have /eqP samey' := same_pvert_y vev' samex2.
    by move: cmp2; rewrite -samey -samey' ltNge le_eqVlt cbev' orbT.
  apply: (le_lt_trans (lef _ cino)).
  by move: evev'; rewrite /lexPt lt_neqAle (negbTE diffx) orbF.
apply/allP => g /mapP[c + /[dup] geq ->]; rewrite !mem_cat => /orP[];
  [ | rewrite orbC => /orP[]]; rewrite /edge_side_prop.
- move=> cfc.
  have cino : c \in open by rewrite ocd mem_cat cfc.
  have vev : valid_edge (high c) (point ev).
    by apply: (proj2 (andP (allP sval _ cino))).
  have evafc : pvert_y (point ev) (high c) < p_y (point ev).
    have := decomposition_above_high_fc oe cbtom adj inbox_e rfo sval cfc.
    by rewrite under_pvert_y // -ltNge.
  have [samex | diffx] := boolP(p_x (point ev) == p_x (point ev')); last first.
    by apply: commondiff=> //; rewrite inE mem_cat cfc ?orbT.
  case: ifP=> [vev' | //].
  have higher : p_y (point ev) < p_y (point ev').
    move: lexev; rewrite /= /lexPtEv /lexPt => /andP[].
    by rewrite lt_neqAle samex /=.
  rewrite (le_lt_trans _ higher); last first.
    by rewrite -(eqP (same_pvert_y vev samex)) le_eqVlt evafc orbT.
  rewrite -(eqP samex).
  have := partedge (high c); rewrite /edge_side_prop map_f // vev => /(_ isT).
  by rewrite evafc.
- move=> clc.
  have cino : c \in open by rewrite ocd !mem_cat clc !orbT.
  have vev : valid_edge (high c) (point ev).
    by apply: (proj2 (andP (allP sval _ cino))).
  have [samex | diffx] :=
         boolP(p_x (point ev) == p_x (point ev')); last first.
    by apply: commondiff => //; rewrite inE mem_cat clc !orbT.
  have yevev' : p_y (point ev) < p_y (point ev').
    move: lexev; rewrite /= /lexPtEv/lexPt lt_neqAle eq_sym=> /andP[] + _.
    by rewrite eq_sym samex.
  move: clae=> /allP/(_ c); rewrite !mem_cat clc ?orbT => /(_ isT) /andP[] _.
  rewrite /end_edge/event_close_edge /= orbA.
  move => /orP[rpt_easy | /hasP[ev2 ev2in /eqP rhc]].
    by apply: rpt_ev' rpt_easy.
  case: ifP => [vce' | //]; case: ifP => [cbev' | _]; last first.
    case: ifP => [caev' | //].
    have := partedge (high c).
    rewrite /edge_side_prop map_f ?cino // vev => /(_ isT).
    suff caev : p_y (point ev) < pvert_y (point ev) (high c).
      rewrite caev ltNge le_eqVlt caev orbT /=.
      by rewrite (eqP samex).
    by move: caev'; rewrite (eqP (same_pvert_y vev samex)); apply: lt_trans.
  rewrite rhc.
  have /orP[// | /andP[samex2 cmp2] ] : lexPt (point ev') (point ev2).
    move: lexev; rewrite /= => /andP[] _; rewrite path_sortedE; last first.
      exact: lexPtEv_trans.
    by move=> /andP[] /allP /(_ ev2 ev2in).
  have := on_pvert (right_on_edge (high c)); rewrite rhc =>samey.
  have /eqP samey' := same_pvert_y vce' samex2.
  by move: cmp2; rewrite -samey -samey' ltNge le_eqVlt cbev' orbT.
move=> /opening_cells_subset /andP[] _; rewrite inE => /orP[/eqP ishe | ].
- have heino : hec \in open by rewrite ocd C D !mem_cat mem_last !orbT.
  move: clae => /allP /(_ hec'); rewrite !mem_cat hec'in orbT.
  move=> /(_ isT) /andP[] _; rewrite E; rewrite /end_edge /event_close_edge /=.
  rewrite orbA => /orP[rpt_easy | /hasP[ev2 ev2in /eqP rhc]].
    by rewrite ishe; apply: rpt_ev' rpt_easy.
  have [_ heaev] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  move: heaev; rewrite strict_under_pvert_y // => heaev.
  have [samex | diffx] := boolP(p_x (point ev) == p_x (point ev')); last first.
    rewrite ishe -B.
    by apply: commondiff => //; rewrite inE eqxx.
  have samey := same_pvert_y vhe samex.
  case: ifP => [vce' | //].
  rewrite ishe.
  have := partedge he; rewrite -B map_f /edge_side_prop; last first.
    by rewrite ocd C D !mem_cat mem_last !orbT.
  rewrite B vhe heaev ltNge le_eqVlt heaev orbT /= (eqP samex) => /(_ isT) ->.
  have : lexPt (point ev') (point ev2).
    move: lexev; rewrite /= => /andP[] _; rewrite path_sortedE; last first.
      exact: lexPtEv_trans.
    by move=> /andP[] /allP /(_ ev2 ev2in).
  move=> /orP[ | /andP[samex2 cmp2] ].
    by rewrite rhc => -> ; case: ifP=> //; case: ifP=> //.
  have := same_pvert_y vce' samex2; rewrite ishe -(eqP samey) => /eqP ->.
  have := on_pvert (right_on_edge he); rewrite rhc => ->.
  by rewrite ltNge le_eqVlt cmp2 orbT /=.
(* last edges: from outgoing. *)
move=> ino.
move: cle => /andP[] /allP /(_ _ ino) + _.
rewrite /end_edge /event_close_edge /= orbA.
move=> /orP[rpt_easy | /hasP[ev2 ev2in /eqP rhc]].
  by apply: rpt_ev' rpt_easy.
case: ifP => [vce' | //].
case: ifP => [cbev' | _]; [ | case: ifP => [caev' | //]].
  have : lexPt (point ev') (point ev2).
    move: lexev; rewrite /= => /andP[] _; rewrite path_sortedE; last first.
      exact: lexPtEv_trans.
    by move=> /andP[] /allP /(_ ev2 ev2in).
    move=> /orP[ | /andP[samex2 cmp2] ].
      by rewrite rhc.
    have := same_pvert_y vce' samex2 => samey2.
    have := on_pvert (right_on_edge ((high c))); rewrite rhc.
    move: cbev'; rewrite (eqP samey2) => + abs; rewrite ltNge le_eqVlt.
    by rewrite abs cmp2 orbT.
have [samex | diffx] := boolP (p_x (point ev) == p_x (point ev')).
  have yevev' : p_y (point ev) < p_y (point ev').
    move: lexev; rewrite /= /lexPtEv/lexPt lt_neqAle eq_sym=> /andP[] + _.
    by rewrite eq_sym samex.
  move: caev'.
  move: (outs (high c) ino) => leftptq.
  have vev : valid_edge (high c) (point ev).
    by rewrite valid_edge_extremities // leftptq.
  have /eqP <- := same_pvert_y vev samex.
  have /on_pvert := left_on_edge (high c); rewrite (eqP leftptq) => ->.
  by move=> /ltW; rewrite leNgt yevev'.
rewrite (eqP (outs (high c) ino)).
by move: lexev => /andP[]; rewrite /lexPtEv/lexPt (negbTE diffx) orbF.
Qed.

Lemma step_keeps_disjoint_open ev open closed open' closed' events :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point ev) ->
  seq_valid open (point ev) ->
  s_right_form open ->
  {in [seq low c | c <- open] ++ [seq high c | c <- open] ++
      outgoing ev &, forall e1 e2, inter_at_ext e1 e2} ->
  {in open &, disjoint_open_cells} ->
  out_left_event ev ->
  all open_cell_side_limit_ok open ->
  edge_side (ev :: events) open ->
  close_alive_edges open (ev :: events) ->
  all (fun x => lexPtEv ev x) events ->
  step ev open closed = (open', closed') ->
  {in open' &, disjoint_open_cells}.
Proof.
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
  by move:(allP sval _ clein)=>/andP[]; rewrite cleq.
have vhe : valid_edge he (point ev).
  by move:(allP sval _ chein)=>/andP[]; rewrite cheq.
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
  have := decomposition_not_contain rfo sval adj
               (bottom_imp_seq_below cbtom inbox_e) oe.
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
have higfc : fc != nil -> high (last dummy_cell fc) = le.
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
    by rewrite botfc // lowbotc pvert_y_bottom.
  have : sorted <=%R [seq pvert_y (point ev) (high c) | c <- extra_bot::open].
    apply adjacent_right_form_sorted_le_y => //=.
      rewrite andbb; apply/andP; split=> //.
      by apply: inside_box_valid_bottom_top=> //; rewrite inE eqxx.
    by rewrite edge_below_refl.
  rewrite /= => pathlt.
  move=> g /mapP[c cin gceq].
  have [s1 [s2 fceq]] : exists s1 s2, fc = s1 ++ c :: s2.
    by move: cin => /splitPr[ x y]; exists x, y.  
  have vertle : pvert_y (point ev) le < p_y (point ev).
    have [+ _]:= l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
    rewrite under_pvert_y; last first.
      rewrite lehcc ccdec; apply: (proj1 (andP (allP sval _ _))) => /=.
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
    move: inbox_e => /andP[] _ /andP[] /andP[] _ ltbot /andP[] _ lttop.
    by move: bottop; rewrite /lexPt !inE;
      move=> /orP[] /eqP ->; rewrite ?lttop ?ltbot.
  move=> /hasP [e' e'in /eqP /[dup]geq ->].
  have : lexPt (point ev) (point e') by apply: (allP lexev).
  move=>/orP[] // /andP[] /eqP xs ys.
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
  have [fch [fct ]] : exists fch fct, fc = fch ++ c :: fct.
        by move: cin => /splitPr [x y]; exists x, y.
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
suff main : {in predU (mem oc) (mem (fc ++ lc)) &, disjoint_open_cells}.
  by move=> c1 c2 inc1 inc2; apply: main;[move: inc1 | move: inc2];
  rewrite !(inE, mem_cat) orbCA.
apply: add_new.
- exact: o_disjointC.
- by have := opening_cells_aux_disjoint eale euhe lein hein lowhigh
              vle vhe osub noc' outlefts srt.
- move=> new old nin; rewrite mem_cat=>/orP[] oin.
    by apply: ocdisjfc.
  by apply: ocdisjlc.

move=> c1 c2 c1in c2in.
by apply: disj; rewrite ocd !mem_cat orbCA -mem_cat; apply/orP; right.
Qed.

Definition pt_at_end (p : pt) (e : edge) :=
  p === e -> p \in [:: left_pt e; right_pt e].

Definition connect_limits (s : seq cell) :=
  sorted [rel c1 c2 | right_limit c1 == left_limit c2] s.
     
Definition edge_covered (e : edge) (os : seq cell) (cs : seq cell) :=
  (exists (opc : cell) (pcc : seq cell), {subset pcc <= cs} /\
    {in rcons pcc opc, forall c, high c = e} /\
    connect_limits (rcons pcc opc) /\
    opc \in os /\
    left_limit (head_cell pcc) = p_x (left_pt e)) \/
  (exists pcc, {subset pcc <= cs} /\
    {in pcc, forall c, high c = e} /\
    connect_limits pcc /\
    left_limit (head_cell pcc) = p_x (left_pt e) /\
    right_limit (last_cell pcc) = p_x (right_pt e)).

Lemma left_limit_closing_cells (cc : seq cell) (p : pt) :
  adjacent_cells cc -> seq_valid cc p ->
  p >>> low (head_cell cc) -> p <<< high (last_cell cc) ->
  all (contains_point p) cc ->
  [seq left_limit i | i <- closing_cells p cc] = [seq left_limit i | i <- cc].
Proof.
move=> adj sval pale puhe allcont.
rewrite closing_cells_single_map => //.
rewrite -map_comp; rewrite -eq_in_map /close_cell => -[] ls rs lo hi cin /=.
move: (allP sval _ cin) => /= /andP[] vlo vhi.
by rewrite (pvertE vlo) (pvertE vhi).
Qed.

Lemma step_keeps_edge_covering e open closed open2 closed2 :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  s_right_form open ->
  out_left_event e ->
  {in open &, injective high} ->
  forall g,
  edge_covered g open closed \/ g \in outgoing e ->
  step e open closed = (open2, closed2) ->
  edge_covered g open2 closed2.
Proof.
move=> cbtom adj inbox_e sval rfo out_e inj_high g; rewrite /step.
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
have := closing_cells_single_map adjcc svalcc.
rewrite ccq [low _]/= [high _]/= -heceq heq leq lu ha => /(_ isT isT).
rewrite -ccq.
have -> : all (contains_point (point e)) cc by apply/allP; exact: cont.
rewrite -/new_closed_cells => /(_ isT) ncseq.
have vlhec : valid_edge (low hec) (point e).
  have hecincc : hec \in cc by rewrite ccq heceq mem_last.
  apply: (proj1 (andP (allP sval hec _))); rewrite ocd !mem_cat.
  by rewrite hecincc !orbT.  
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
  left; exists (last_cell new_cells), (rcons pcc1 (last_cell new_closed_cells)).
  split.
    move=> c; rewrite /closed2 !(mem_rcons, mem_cat, inE).
    move=> /orP[/eqP -> | /subp1 -> //].
    by rewrite ncseq ccq /last_cell /= mem_last orbT.
  split.
    move=> c; rewrite !(mem_rcons, inE) => /orP[/eqP |/orP[/eqP | inpcc1]];
        last by apply: ph; rewrite mem_rcons inE inpcc1 orbT.
      move=> ->; rewrite ghe.
      by apply/eqP; apply: (higher_edge_new_cells out_e erefl vle vhe).
    rewrite ncseq ccq /last_cell /= => ->.
    rewrite last_map -heceq /close_cell.
    by rewrite (pvertE vlhec) heq (pvertE vhe) /= ghe.
  split.
      have last_conn : right_limit (last_cell new_closed_cells) =
                 left_limit (last_cell new_cells).
        rewrite ncseq /last_cell ccq /= last_map -heceq /close_cell.
        rewrite (pvertE vlhec) heq (pvertE vhe) /=.
        set rl := right_limit _.
        have -> : rl = p_x (point e) by rewrite /rl; case: ifP; case: ifP=> //.
        apply/esym => {rl}.
        apply: (@opening_cells_left _ (outgoing e) le he).
        move: (opening_cells_not_nil (outgoing e) vle vhe).
        rewrite -/new_cells.
        by case: (new_cells) => [ | a l ]; rewrite //= mem_last.
      case pcc1q : pcc1 => [ | a l]; first by rewrite /= last_conn eqxx.
      rewrite /= -cats1 cat_path last_rcons /= last_conn eqxx !andbT.
      rewrite -cats1 cat_path /= andbT.
      move: (cl); rewrite pcc1q /= -cats1 cat_path => /andP[] -> /=.
      rewrite andbT => /eqP ->.
      have := left_limit_closing_cells adjcc svalcc.
      rewrite hdcclo lcchi => /(_ lu ha).
      have -> : all (contains_point (point e)) cc by apply/allP; exact: cont.
      move=> /(_ isT).

      move: cl; rewrite a.
      move: 
      rewrite /new_cells.
      rewrite (@opening_cells_left (point e) (outgoing e) le he); last first.
        move: (opening_cells_not_nil (outgoing e) vle vhe).
        rewrite -/new_cells.
        by case: (new_cells) => [ | a l ]; rewrite /last_cell //= mem_last.

      rewrite ccq /last_cell /= last_map /close_cell.
      set rl := right_limit _.
      have -> : rl = p_x (point e).
        rewrite /rl -heceq (pvertE vlhec) heq (pvertE vhe) /=.
        by case: ifP => [latpointe | lnotpointe];
           case: ifP => [hatpointe | hnotpointe].
      rewrite eq_sym andbT; apply/eqP.


End proof_environment.

Lemma add_event_preserve_first p e inc ev evs :
  (0 < size (add_event p e inc (ev :: evs)))%N /\
  (point (head ev (add_event p e inc (ev :: evs))) = p \/
   point (head ev (add_event p e inc (ev :: evs))) = point ev).
Proof.
rewrite /=.
case: ev => [p1 o1].
have [/eqP -> | /eqP pnp1] := boolP(p == p1).
  by split; case: inc => //=; left.
have [pltp1 /= | pnltp1] := boolP(p_x p < p_x p1).
  split.
    by case: inc.
  by case:inc; left.
have [/eqP pxqpx1 /= | pxnpx1 /=] := boolP (p_x p == p_x p1).
  have [/eqP pyltpy1 /= | pynltpy1 /=] := boolP (p_y p < p_y p1).
    by case:inc; (split;[ | left]).
  by split;[ | right].
by split;[ | right].
Qed.

Lemma add_event_sort p e inc evs : sorted lexPtEv evs ->
  sorted lexPtEv (add_event p e inc evs).
Proof.
elim: evs => [ | ev1 evs Ih /=].
  by case: inc.
move=> path_evs.
have [/eqP pp1 | /eqP pnp1] := boolP(p == point ev1).
  case: inc Ih.
    by case: evs path_evs => [ | ev2 evs'].
  by case: evs path_evs => [ | ev2 evs'].
move/path_sorted/Ih: (path_evs) {Ih} => Ih.
have [ pltp1 | pnltp1] /= := boolP(p_x p < p_x (point ev1)).
  by case: inc {Ih}=> /=; (apply/andP; split=> //); rewrite /lexPtEv /lexPt /= pltp1.
have [/eqP pp1 | pnp1'] /= := boolP (p_x p == p_x (point ev1)).
  have pyneq : p_y p != p_y (point ev1).
    apply/eqP=> pp1'; case pnp1.
    move: p (point ev1) {pnp1 Ih pnltp1} pp1 pp1'.
    by move=> [a b][c d] /= -> ->.
  have [ pltp1 | pnltp1'] /= := boolP(p_y p < p_y (point ev1)).
    by case: (inc); rewrite /= path_evs andbT /lexPtEv /lexPt /= pp1 eqxx pltp1 orbT.
  have p1ltp : p_y (point ev1) < p_y p.
    by rewrite ltNge le_eqVlt negb_or pyneq pnltp1'.
  case evseq : evs => [ | [p2 o2] evs2].
    by case: (inc)=> /=; rewrite /lexPtEv /lexPt /= pp1 eqxx p1ltp orbT.
  rewrite -evseq.
  case aeq : (add_event p e inc evs) => [ | e' evs3].
    have := add_event_preserve_first p e inc
           {| point := p2; outgoing := o2 |} evs2.
      by rewrite -evseq aeq => [[]].
  case: (add_event_preserve_first p e inc
         {| point := p2; outgoing := o2 |} evs2)=> _.
  rewrite -evseq aeq /= => [] [eqp | eqp2].
    apply/andP; split; last by move: Ih; rewrite aeq.
    by rewrite /lexPtEv /lexPt eqp pp1 eqxx p1ltp orbT.
  apply/andP; split; last by move: Ih; rewrite aeq.
  move: path_evs; rewrite evseq /= andbC => /andP[] _.
  by rewrite /lexPtEv /= eqp2.
have p1ltp : p_x (point ev1) < p_x p.
  by rewrite ltNge le_eqVlt negb_or pnp1' pnltp1.
case evseq : evs => [ | [p2 o2] evs2].
  by case: (inc)=> /=; rewrite /lexPtEv /lexPt /= p1ltp.
case aeq : (add_event p e inc evs) => [ | e' evs3].
  case: (add_event_preserve_first p e inc
       {| point := p2; outgoing := o2 |} evs2).
  by rewrite -evseq aeq.
case: (add_event_preserve_first p e inc
     {| point := p2; outgoing := o2 |} evs2) => _.
have path_e'evs3 : path lexPtEv e' evs3 by move: Ih; rewrite aeq.
rewrite -evseq aeq /= => [][e'p | e'p2]; rewrite path_e'evs3 andbT.
  by rewrite /lexPtEv /lexPt e'p p1ltp.
by move: path_evs; rewrite evseq /= andbC /lexPtEv e'p2=> /andP[].
Qed.

Lemma sorted_edges_to_events s :
   sorted (@lexPt R) [seq point x | x <- edges_to_events s].
Proof.
have /mono_sorted -> : {mono point : x y / lexPtEv x y >-> lexPt x y} by [].
by elim: s => [ | g s Ih] //=; do 2 apply: add_event_sort.
Qed.

Lemma add_event_preserve_ends bottom top p e inc evs ed :
  end_edge bottom top ed evs ->
  end_edge bottom top ed (add_event p e inc evs).
Proof.
have [excp | norm ] := boolP(ed \in [:: bottom; top]).
  by rewrite /end_edge excp.
rewrite /end_edge (negbTE norm) /=.
elim: evs => [// | ev evs Ih] /= /orP[|];
  repeat (case: ifP => _);
   rewrite /=/event_close_edge /=; try (move=> -> //); rewrite ?orbT //.
by move=> ?; rewrite Ih ?orbT.
Qed.

Lemma add_event_inc bottom top evs ed :
  end_edge bottom top ed (add_event (right_pt ed) ed true evs).
Proof.
elim: evs => [ | ev evs Ih] /=.
  by rewrite /end_edge /= /event_close_edge /= eqxx orbT.
case: ifP=> [/eqP <- | ].
  by rewrite /end_edge /= /event_close_edge /= eqxx orbT.
repeat (case: ifP=> _); rewrite /end_edge/=/event_close_edge ?eqxx ?orbT //.
move=> _; move: Ih; rewrite /end_edge/=/event_close_edge => /orP [] -> //.
by rewrite !orbT.
Qed.

Lemma close_edges_from_events_inc bottom top evs p ed :
 close_edges_from_events bottom top evs ->
 close_edges_from_events bottom top (add_event p ed true evs).
Proof.
elim: evs => /= [ // | ev evs Ih /andP [clev clevs]].
move: Ih=> /(_ clevs) Ih.
case: ifP=> _ /=; first by rewrite clevs andbT; exact clev.
case: ifP=> _ /=; first by rewrite clevs andbT; exact clev.
case: ifP=> _ /=; first by rewrite clevs andbT; exact clev.
rewrite Ih andbT.
apply/allP=> ed' edin'.
move: (allP clev ed' edin')=> /orP[]; first by rewrite /end_edge => ->.
by move=> it; rewrite add_event_preserve_ends // /end_edge it ?orbT.
Qed.

Lemma add_edge_close_edges_from_events bottom top evs ed :
  close_edges_from_events bottom top evs ->
  close_edges_from_events bottom top
    (add_event (left_pt ed) ed false (add_event (right_pt ed) ed true evs)).
Proof.
have no_eq : left_pt ed == right_pt ed = false.
    by apply/negP=> /eqP abs_eq; have := edge_cond ed; rewrite abs_eq ltxx.
elim: evs => [/= _ | ev evs Ih].
  rewrite no_eq edge_cond /=.
  by rewrite /close_out_from_event /= /end_edge/=/event_close_edge eqxx orbT.
move=> tmp; rewrite /= in tmp; case/andP: tmp=> [clev clevs].
move: Ih=> /(_ clevs) Ih.
have : end_edge bottom top ed (add_event (right_pt ed) ed true (ev :: evs)).
  by apply: add_event_inc.
rewrite [add_event (right_pt _) _ _ _]add_event_step.
lazy zeta.
case: ifP=> [/eqP <- /= | cnd1].
  rewrite no_eq edge_cond /=.
  rewrite /close_out_from_event /= /end_edge/=/event_close_edge.
  rewrite eqxx orbT /= clevs andbT=> _; exact: clev.
case: ifP=> cnd2 /=.
  rewrite no_eq edge_cond /=.
  rewrite /close_out_from_event /= => -> /=; rewrite clevs andbT; exact: clev.
case: ifP=> cnd3 ended /=.
  rewrite no_eq edge_cond.
  rewrite close_edges_from_events_step.
  apply/andP; split; last by rewrite /= clev clevs.
  by rewrite /close_out_from_event/= ended.
case: ifP=> cnd4.
  rewrite close_edges_from_events_step /close_out_from_event/=.
  rewrite close_edges_from_events_inc ?andbT ?clevs //.
  apply/andP; split; last first.
    apply/allP=> x xin.
    move/allP: clev=> /(_ x xin) closed.
    by rewrite add_event_preserve_ends ?orbT.
  by rewrite add_event_inc.
case: ifP=> cnd5.
  rewrite close_edges_from_events_step; apply/andP; split.
    by rewrite /close_out_from_event /= ended.
  rewrite close_edges_from_events_step; apply/andP; split.
    apply/allP=> x xin; apply: add_event_preserve_ends.
    by move/allP: clev=> /(_ x xin).
  by apply: close_edges_from_events_inc.
case: ifP=> cnd6.
  rewrite close_edges_from_events_step; apply/andP; split.
    by rewrite /close_out_from_event /= ended.
  rewrite close_edges_from_events_step; apply/andP; split.
    apply/allP=> x xin; apply: add_event_preserve_ends.
    by move/allP: clev=> /(_ x xin).
  by apply: close_edges_from_events_inc.
rewrite close_edges_from_events_step; apply/andP; split.
  rewrite /close_out_from_event.
  apply/allP=> x xin.
  do 2 apply:add_event_preserve_ends.
  by move/allP: clev; apply.
by apply: Ih.
Qed.

Lemma edges_to_events_wf (bottom top : edge)(s : seq edge) :
  close_edges_from_events bottom top (edges_to_events s).
Proof.
elim : s => [ // | e s Ih /=].
by apply: add_edge_close_edges_from_events.
Qed.

Lemma edges_to_events_no_loss (s : seq edge) :
  perm_eq s (events_to_edges (edges_to_events s)).
Proof.
have add_inc evs p ed:
  perm_eq (events_to_edges evs)
    (events_to_edges (add_event p ed true evs)).
  elim: evs => [/= | ev evs Ih]; first by apply: perm_refl.
  rewrite /events_to_edges /=.
  by repeat (case: ifP=> _ //=); rewrite perm_cat2l Ih.
have add_out evs p ed:
  perm_eq (ed :: events_to_edges evs)
     (events_to_edges (add_event p ed false evs)).
  elim: evs => [/= | ev evs]; first by apply: perm_refl.
  rewrite /events_to_edges /= => Ih.
  repeat (case: ifP => //=); move => ? ? ?.
  rewrite -[ed :: outgoing ev ++ _]/([:: ed] ++ outgoing ev ++ _).
  by rewrite perm_catCA perm_cat2l Ih.
elim: s => /= [// | ed s Ih]; rewrite -(perm_cons ed) in Ih.
apply/(perm_trans Ih)/(perm_trans _ (add_out _ (left_pt ed) _)).
by rewrite perm_cons; apply: add_inc.
Qed.

Lemma edges_to_events_no_crossing s :
  {in s &, no_crossing R} ->
  {in events_to_edges (edges_to_events s) &, no_crossing R}.
Proof.
by apply: sub_in2=> x; rewrite (perm_mem (edges_to_events_no_loss s)).
Qed.

Lemma step_sub_open_edges bottom top open closed open' closed' ev:
  cells_bottom_top bottom top open ->
  adjacent_cells open ->
  inside_box bottom top (point ev) ->
  step ev open closed = (open', closed') ->
  {subset [seq low i | i <- open'] ++ [seq high i | i <- open']
      <= [seq low i | i <- open] ++ [seq high i | i <- open] ++
         outgoing ev}.
Proof.
move=> cbtom adj inbox_e.
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
case/orP: tmp; rewrite !memf !mem_cat; move=>/orP[->|]; rewrite ?orbT //.
  move/mapP=> [c cin ->].
  have:= opening_cells_aux_subset cin; rewrite inE => /andP[] /orP[/eqP -> | +] _. 
    by rewrite map_f ?orbT //.
  by rewrite (perm_mem (permEl (perm_sort _ _))) => ->; rewrite ?orbT.
move/mapP=> [c cin ->].
have:= opening_cells_aux_subset cin.
rewrite !inE => /andP[] _ /orP[/eqP -> | +].
  by rewrite map_f ?orbT //.
by rewrite (perm_mem (permEl (perm_sort _ _))) => ->; rewrite ?orbT.
Qed.

Lemma out_left_add_event p g b evs:
    p = (if b then right_pt g else left_pt g) ->
    {in evs, forall ev, out_left_event ev} ->
    {in add_event p g b evs, forall ev, out_left_event ev}.
Proof.
move=> ->.
elim: evs => [ | ev evs Ih] acc.
  move=> /= ev; case:b; rewrite inE => /eqP -> e //=.
  by rewrite inE => /eqP ->; rewrite eqxx.
rewrite /=; case: ifP=> [/eqP pev | ] ev'.
  case bval: (b); rewrite /= inE => /orP[/eqP ev'ev | ev'inevs].
  - have -> : ev' = ev by rewrite ev'ev; case: (ev).
    by apply: acc; rewrite inE eqxx.
  - by apply: acc; rewrite inE ev'inevs orbT.
  - move=> g2; rewrite ev'ev /= inE=> /orP[/eqP -> | ].
    * by rewrite -pev bval eqxx.
    by apply: acc; rewrite inE eqxx.
  by apply: acc; rewrite inE ev'inevs orbT.
case: ifP => [athead | later].
  case bval: (b) => ev2; rewrite inE => /orP[].
  - by move/eqP=> -> g2.
  - by apply: acc.
  - by move/eqP=> -> g2 /=; rewrite inE=> /eqP ->; rewrite eqxx.
  by apply: acc.
case: ifP => [athead' | later'].
  case bval: (b) => ev2; rewrite inE => /orP[].
  - by move/eqP=> -> g2.
  - by apply: acc.
  - by move/eqP=> -> g2 /=; rewrite inE=> /eqP ->; rewrite eqxx.
  by apply: acc.
move=> ev2; rewrite inE=> /orP[/eqP -> | ev2intl].
  by apply: acc; rewrite inE eqxx.
apply: Ih=> //.
by move=> ev3 ev3in; apply: acc; rewrite inE ev3in orbT.
Qed.

Lemma out_left_edges_to_events s:
  {in edges_to_events s, forall ev, out_left_event ev}.
Proof.
elim: s => [// | g s Ih] /=.
have Ih' := @out_left_add_event (right_pt g) g true _ erefl Ih.
by have Ih'' := @out_left_add_event (left_pt g) g false _ erefl Ih'.
Qed.

Lemma add_event_point_subset (s : mem_pred pt) p g b evs :
  {subset [seq point ev | ev <- evs] <= s} ->
  p \in s ->
  {subset [seq point ev | ev <- add_event p g b evs] <= s}.
Proof.
elim: evs => [ | ev evs Ih].
  by move=> _ pin /=; case: ifP => /= bval p'; rewrite inE=> /eqP ->.
move=> cnd pin; have cnd' : {subset [seq point ev' | ev' <- evs] <= s}.
  by move=> p' p'in; apply: cnd; rewrite inE p'in orbT.
have Ih' := Ih cnd' pin; clear Ih.
have evin : point ev \in s by apply: cnd; rewrite !inE eqxx.
rewrite /=; (repeat (case: ifP=> _))=> p'; rewrite /= !inE;
  (repeat(move=>/orP[])); try solve[move=> /eqP -> // | by apply: cnd'].
apply: Ih'.
Qed.

Lemma edges_to_events_subset (s : mem_pred pt) (gs : seq edge) :
  {subset [seq left_pt g | g <- gs] <= s} ->
  {subset [seq right_pt g | g <- gs] <= s} ->
  {subset [seq point ev | ev <- edges_to_events gs] <= s}.
Proof.
elim: gs => [// | g gs Ih].
rewrite /=.
move=> cndl cndr.
have cndl' : {subset [seq left_pt g | g <- gs] <= s}.
  by move=> x xin; apply: cndl; rewrite inE xin orbT.
have cndr' : {subset [seq right_pt g | g <- gs] <= s}.
  by move=> x xin; apply: cndr; rewrite inE xin orbT.
have cndleft : left_pt g \in s by apply: cndl; rewrite inE eqxx.
have cndright : right_pt g \in s by apply: cndr; rewrite inE eqxx.
have Ih' := Ih cndl' cndr'; clear Ih.
by apply: add_event_point_subset;[apply: add_event_point_subset | ].
Qed.

Lemma inside_box_left_ptsP bottom top p :
  inside_box bottom top p -> 
  p_x (last dummy_pt (leftmost_points bottom top)) <= p_x p.
Proof.
move=> /andP[] _ /andP[] valb valt.
move: valb valt=> /andP[] pgelb plerb /andP[] pgelt plert.
rewrite /leftmost_points; case: ifP=> cmpl.
  have /exists_point_valid [p1 p1P] : valid_edge bottom (left_pt top).
    rewrite /valid_edge (ltW cmpl) /=.
    by apply: ltW; apply: (lt_trans pgelt).
  rewrite p1P /=; apply/ltW.
  by move: (intersection_on_edge p1P) => [] _ <-.
move/negbT: cmpl; rewrite -leNgt=>cmpl.
have /exists_point_valid [p1 p1P] : valid_edge top (left_pt bottom).
  rewrite /valid_edge cmpl /=.
  by apply/ltW; apply: (lt_trans pgelb).
by rewrite p1P /=; apply/ltW.
Qed.
  
Lemma start_cover (bottom top : edge) (s : seq edge) closed open :
  bottom <| top ->
  {in bottom :: top :: s &, no_crossing R} ->
  all (inside_box bottom top) [seq left_pt x | x <- s] ->
  all (inside_box bottom top) [seq right_pt x | x <- s] ->
  start (edges_to_events s) bottom top = (closed, open) ->
  forall p, inside_box bottom top p ->
  has (inside_closed_cell p) closed || has (inside_open_cell p) open.
Proof.
move=> boxwf nocs leftin rightin; rewrite /start.
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
(* have : {in [seq low i | i <- op0] ++
       [seq high i | i <- op0] ++ 
       flatten [seq outgoing i | i <- evs] &,
     no_crossing R}.
  rewrite /=; move: nocs; apply sub_in2.
  move=> x; rewrite !inE => /orP[-> //| [/orP[-> // | ]]]; rewrite ?orbT//.
  by rewrite -stoevs orbA orbC => ->. *)
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
  rewrite /op0 inE=> /eqP -> /=.
  by apply/inside_box_left_ptsP/(allP evsin0).
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
  apply/andP; split;[apply/andP; split => /= | move=>/=].
  - by apply: underWC; move: inbox_q=> /andP[] /andP[].
  - by apply: underW; move: inbox_q=> /andP[] /andP[].
  - rewrite /open_limit /=.
    case: (ltrP  (p_x (right_pt bottom)) (p_x (right_pt top))) => _.
    rewrite inside_box_left_ptsP //.
    by move: inbox_q => /andP[] _ /andP[] /andP[] _ /ltW ->.
  rewrite inside_box_left_ptsP //.
  by move: inbox_q => /andP[] _ /andP[] _ /andP[] _ /ltW ->.
move: cov0 evsin0 sval0 btm_left0; move=> {stoevs}.
elim: evs op0 cl0 => [ | ev evs' Ih]
   op cl main evsin sval btm_left clev oute noc clae rfo adj cbtom sortev.
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
           noc btm_left' stepeq cov.
  by [].
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
      by move=>/andP[]/allP/(_ (point e') (map_f point e'q))/lexPtW.
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
    move/(step_sub_open_edges cbtom adj inbox_e stepeq)=> it.
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
by have := Ih _ _ cov' evsinr svalr btm_leftr clevr outer nocr claer rfor adjr
        cbtomr sortev' scaneq.
Qed.

End working_environment.
