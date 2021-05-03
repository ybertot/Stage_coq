
From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef.

Open Scope ring_scope.


Record pt := Bpt {p_x : rat; p_y : rat}.

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
     move: p1 p2. rewrite -a1a2 -b1b2 => p1 p2.
     rewrite (eqtype.bool_irrelevance p1 p2).
     by apply: ReflectT.
   by apply: ReflectF=> [][].
by apply: ReflectF=>[][].
Qed.

Canonical edge_eqType := EqType edge (EqMixin edge_eqP).

Record cell := Bcell  {pts : list pt; low : edge; high : edge}.

Definition cell_eqb (ca cb : cell) : bool :=
  let: Bcell ptsa lowa higha := ca in
  let: Bcell ptsb lowb highb:= cb in
  (ptsa == ptsb) && (lowa == lowb) && (higha == highb).


Lemma cell_eqP : Equality.axiom cell_eqb.
Proof.
rewrite /Equality.axiom.
move => [ptsa lowa higha] [ptsb lowb highb] /=.
have [/eqP <-|/eqP anb] := boolP(ptsa == ptsb).
  have [/eqP <-|/eqP anb] := boolP(lowa == lowb).
    have [/eqP <-|/eqP anb] := boolP(higha == highb).
      by apply:ReflectT.
    by apply : ReflectF => [][].
  by apply: ReflectF=> [][].
by apply: ReflectF=> [][].
Qed.

Canonical cell_eqType := EqType cell (EqMixin cell_eqP).

Record event := Bevent {point : pt; incoming : seq edge; outgoing : seq edge}.

Definition event_eqb (ea eb : event) : bool :=
  let: Bevent pta inca outa := ea in
  let: Bevent ptb incb outb := eb in
  (pta == ptb) && (inca == incb) && (outa == outb).

Lemma event_eqP : Equality.axiom event_eqb.
Proof.
rewrite /Equality.axiom.
move => [pta inca outa] [ptb incb outb] /=.
have [/eqP <-|/eqP anb] := boolP(pta == ptb).
  have [/eqP <-|/eqP anb] := boolP(inca == incb).
    have [/eqP <-|/eqP anb] := boolP(outa == outb).
      by apply:ReflectT.
    by apply : ReflectF => [][].
  by apply: ReflectF=> [][].
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
  | nil => if inc then [:: Bevent p [:: e] [::]]
           else [:: Bevent p [::] [:: e]]
  | ev1 :: evs' =>
    let p1 := point ev1 in
    if p == p1 then
      if inc then Bevent p1 (e :: incoming ev1) (outgoing ev1) :: evs'
      else Bevent p1 (incoming ev1) (e :: outgoing ev1) :: evs' else
    if p_x p < p_x p1 then
      if inc then
        Bevent p [:: e] [::] :: evs else
        Bevent p [::] [:: e] :: evs
    else if (p_x p == p_x p1) && (p_y p < p_y p1) then
       if inc then
         Bevent p [:: e] [::] :: evs else
         Bevent p [::] [:: e] :: evs else
    ev1 :: add_event p e inc evs'
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


(* returns true if p is under A B *)
Definition pue_formula (p : pt) (a : pt) (b : pt) : rat :=
  let: Bpt p_x p_y := p in
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
     (b_x * p_y - p_x * b_y - (a_x * p_y - p_x * a_y) + a_x * b_y - b_x * a_y).

(* returns true if p is under e *)
Definition point_under_edge (p : pt) (e : edge) : bool :=
  let: Bedge a b _ := e in 
  pue_formula p a b <=0.

(*returns true if e1 is under e2*)
Definition compare_incoming (e1 e2 : edge) : bool :=
  let: Bedge a _ _ := e1 in
    point_under_edge a e2.

(*returns true if e1 is under e2*)
Definition compare_outgoing (e1 e2 : edge) : bool :=
  let: Bedge _ b _ := e1 in
  point_under_edge b e2.



Check @Bedge (Bpt 3%:Q 4%:Q) (Bpt 4%:Q 4%:Q) isT.

Compute compare_incoming  (@Bedge  (Bpt 2%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT) (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT ).


Compute compare_outgoing (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 1%:Q) isT ) (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT).

Definition sort_incoming (inc : seq edge) : seq edge :=
  sort compare_incoming inc.
Definition sort_outgoing (out : seq edge) : seq edge :=
  sort compare_outgoing out.


Definition E1 : edge := (@Bedge  (Bpt 2%:Q 5%:Q) (Bpt 3%:Q 3%:Q) isT).
Definition E2 : edge := (@Bedge  (Bpt (@Rat (7%:Z, 3%:Z) isT)  10%:Q) (Bpt 3%:Q 3%:Q) isT).
Definition E3 : edge := (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT).

Definition sorted_inc := map left_pt (sort_incoming [:: E1; E2; E3]).
Eval lazy in sorted_inc. 

Definition E4 : edge := (@Bedge  (Bpt 2%:Q 3%:Q) (Bpt 4%:Q 6%:Q) isT).
Definition E5 : edge := (@Bedge  (Bpt 2%:Q 3%:Q) (Bpt 5%:Q 3%:Q) isT).
Definition E6 : edge := (@Bedge  (Bpt 2%:Q 3%:Q) (Bpt 4%:Q 3%:Q) isT).
Definition sorted_out := map right_pt (sort_outgoing [:: E4; E5; E6]).
Eval lazy in sorted_out.


Section ring_sandbox.

Variable R : fieldType.
Definition R' := (R : Type).

Let mul : R' -> R' -> R' := @GRing.mul _.
Let add : R' -> R' -> R' := @GRing.add _.
Let sub : R' -> R' -> R' := (fun x y => x - y).
Let opp : R' -> R' := @GRing.opp _.
Let zero : R' := 0.
Let one : R' := 1.


Let R2_theory :=
   @mk_rt R' zero one add mul sub opp
    (@eq R')
    (@add0r R) (@addrC R) (@addrA R) (@mul1r R) (@mulrC R)
      (@mulrA R) (@mulrDl R) (fun x y : R' => erefl (x - y)) (@addrN R).

Add Ring R2_Ring : R2_theory.

Ltac mc_ring :=
rewrite ?mxE /= ?(expr0, exprS, mulrS, mulr0n) -?[@GRing.add _]/add
    -?[@GRing.mul _]/mul
    -?[@GRing.opp _]/opp -?[1]/one -?[0]/zero;
match goal with |- @eq ?X _ _ => change X with R' end;
ring.

Let inv : R' -> R' := @GRing.inv _.
Let div : R' -> R' -> R' := fun x y => mul x (inv y).

Definition R2_sft : field_theory zero one add mul sub opp div inv (@eq R').
Proof.
constructor.
- exact R2_theory.
- have // : one <> zero by apply/eqP; rewrite oner_eq0.
- have // : forall p q : R', div p q = mul p (inv q) by [].
- have // : forall p : R', p <> zero -> mul (inv p) p = one.
  by move=> *; apply/mulVf/eqP.
Qed.

Add Field Qfield : R2_sft.

Ltac mc_field :=
rewrite ?mxE /= ?(expr0, exprS, mulrS, mulr0n) -?[@GRing.add _]/add
    -?[@GRing.mul _]/mul -[@GRing.inv _]/inv
    -?[@GRing.opp _]/opp -?[1]/one -?[0]/zero;
match goal with |- @eq ?X _ _ => change X with R' end;
field.

Example field_playground (x y : R' ) : x != 0 -> y != 0 -> (x * y) / (x * y) = 1.
Proof.
move=> xn0 yn0; mc_field.
by split; apply/eqP.
Qed.

(* returns true if p is under A B *)
Definition pue_f (p_x p_y a_x a_y b_x b_y : R')  : R' :=
     (b_x * p_y - p_x * b_y - (a_x * p_y - p_x * a_y) + a_x * b_y - b_x * a_y).

Lemma pue_f_o p_x p_y a_x a_y b_x b_y:  pue_f p_x p_y a_x a_y b_x b_y = - pue_f  b_x b_y a_x a_y p_x p_y.
Proof.
  rewrite /pue_f.
  mc_ring.
Qed.

Lemma pue_f_c p_x p_y a_x a_y b_x b_y:  pue_f p_x p_y a_x a_y b_x b_y =  pue_f   b_x b_y p_x p_y a_x a_y.
Proof.
  rewrite /pue_f.
  mc_ring.
Qed.

Lemma pue_f_inter p_x  a_x a_y b_x b_y :  b_x != a_x -> (pue_f p_x ((p_x - a_x)* ((b_y - a_y)/(b_x - a_x)) + a_y) a_x a_y b_x b_y) == 0.
Proof.
rewrite /pue_f.
rewrite -subr_eq0 => h.
set slope := (_ / _).
rewrite /pue_f.
rewrite (mulrDr b_x).
rewrite (mulrDr a_x).
rewrite -(orbF (_==0)).
rewrite -(negbTE   h).
rewrite -mulf_eq0 .
rewrite ! ( mulrBl (b_x - a_x), fun x y => mulrDl  x y (b_x - a_x)).

rewrite /slope !mulrA !mulfVK //.
apply/eqP; mc_ring.
Qed.

Lemma pue_f_inters p_x p_y a_x a_y b_x b_y  :  b_x != a_x -> p_y = ((p_x - a_x) * ((b_y - a_y) / (b_x - a_x)) + a_y) ->
pue_f p_x p_y a_x a_y b_x b_y == 0.
Proof.
move => h ->.
by apply pue_f_inter; rewrite h.
Qed.


End ring_sandbox.

Lemma pue_formula_opposite a b d:  pue_formula d a b = - pue_formula b a d.
Proof.
  move: a b d => [ax ay] [b_x b_y] [dx dy]/=.
  apply :pue_f_o.
Qed.

Lemma pue_formula_cycle a b d : pue_formula d a b = pue_formula b d a.
Proof.
  move: a b d => [ax ay] [b_x b_y] [dx dy]/=.
  apply :pue_f_c.
Qed.


Lemma compare_outgoing_total p : {in [pred e | left_pt e == p] &, total compare_outgoing} .
Proof.
Check sort_sorted_in.
rewrite /total.
move => ab cd /eqP lp /eqP lp2.
have: left_pt ab = left_pt cd.
  by rewrite lp lp2.
move => h {lp lp2}.
rewrite -implyNb.
apply /implyP.
rewrite /compare_outgoing /point_under_edge.
move : ab cd h => [a b ab][c d cd] /= h.
rewrite -ltNge h.
rewrite pue_formula_opposite/=.
rewrite oppr_gt0.
apply ltW.
Qed.

Lemma compare_incoming_total p : {in [pred e | right_pt e == p] &, total compare_incoming} .
Proof.

rewrite /total.
move => ab cd /eqP lp /eqP lp2.
have: right_pt ab = right_pt cd.
  by rewrite lp lp2.
move => h {lp lp2}.
rewrite -implyNb.
apply /implyP.
rewrite /compare_incoming /point_under_edge.
move : ab cd h => [a b ab][c d cd] /= h.
rewrite h -ltNge pue_formula_opposite -pue_formula_cycle.
rewrite oppr_gt0.
apply ltW.
Qed.

Lemma sort_out : forall p s, all [pred e | left_pt e == p] s ->
  sorted compare_outgoing (sort compare_outgoing s).
Proof.
rewrite /=.
move => p s.

apply /sort_sorted_in /compare_outgoing_total.
Qed.

Lemma sort_inc : forall p s, all [pred e | right_pt e == p] s ->
  sorted compare_incoming (sort compare_incoming s).
Proof.
rewrite /=.
move => p s.
apply /sort_sorted_in /compare_incoming_total.
Qed.

Definition valid_edge e x := (p_x (left_pt e) <= x) /\ (x <= p_x (right_pt e)).
Definition valid_cell c x := (valid_edge (low c) x) /\ (valid_edge (high c) x).

(* returns the point of the intersection between a vertical edge
 intersecting p and the edge e if it exists, None if it doesn't *)
Definition vertical_intersection_point (p : pt) (e : edge) : option pt := 
  let: Bpt p_x p_y := p in
  let: Bedge a b _ := e in
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
  if (p_x < a_x) || (b_x < p_x) then None else 
  Some(Bpt p_x ((p_x - a_x) * ((b_y - a_y) / (b_x - a_x)) + a_y)).

Lemma vertical_none p e :
  let: Bpt p_x p_y := p in
  let: Bedge a b _ := e in
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
 (p_x < a_x) || (b_x < p_x) -> vertical_intersection_point p e = None.
Proof.
move: p e => [px py] [[ax ay] [b_x b_y] ab] h /=.
by apply /ifT.
Qed.


Definition point_on_edge (p: pt) (e :edge) : bool :=
  let: Bedge a b _ := e in
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
  pue_formula p a b == 0.

Lemma vertical_correct p e : 
let: Bpt pt_x pt_y := p in
  let: Bedge a b _ := e in
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
    match(vertical_intersection_point p e) with None => ((pt_x < a_x) || (b_x < pt_x)) | Some(i) => point_on_edge i e end.
Proof.
move: p e => [ptx pty] [[ax ay] [bx b_y]  /=ab] .
case : ifP => h.
by [].
have: ax != bx.
rewrite mc_1_10.Num.Theory.neqr_lt ab //=.
rewrite /pue_formula.
set py := ((b_y - ay) / (bx - ax) * ptx + (ay - (b_y - ay) / (bx - ax) * ax)).
move => h2.

apply pue_f_inters.
by apply /eqP /nesym /eqP .
by rewrite /py.
Qed.

Definition dummy_event := Bevent (Bpt 0%:Q 0%:Q) [::] [::].
Definition dummy_edge : edge := (@Bedge  (Bpt 0%:Q 0%:Q) (Bpt 1%:Q 0%:Q) isT).
Definition dummy_cell : cell := (@Bcell  ((Bpt 0%:Q 0%:Q)::[::]) dummy_edge dummy_edge).

(* if a cell doesn't contain a point, then either both edges are strictly under p or strictly over p *)
Definition contains_point (p : pt) (c : cell)  : bool :=
   let e1 := low c in
   let e2 := high c in
   let: Bedge a b _ := e1 in 
   let: Bedge c d _ := e2 in 
      pue_formula p a b * pue_formula p c d <= 0.

Fixpoint contains (A : eqType) (s : seq A) (a : A) : bool :=
   match s with
     | [::] => false
     | b :: m => (b == a) || (contains m a)
   end.


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
                        Bcell  ((no_dup_seq [:: p; p1])++(pts c)) (low c) (high c)::[::]
                    end
       | c::q =>  Bcell  (p::(pts c)) (low c) (high c)::closing_rest p q
    end.



Definition closing_cells (p : pt) (contact_cells: seq cell) : (seq cell) :=
    match contact_cells with
      | [::] => [::]
      | [:: only_cell] => 
                      let op0 := vertical_intersection_point p (low only_cell) in 
                      let op1 := vertical_intersection_point p (high only_cell) in
                      match (op0,op1) with 
                          |(None,_) |(_,None)=> [::]
                          |(Some(p0),Some(p1)) =>
                              Bcell  ((no_dup_seq [:: p0; p; p1])++(pts only_cell)) (low only_cell) (high only_cell)::[::]
                      end
      | c::q => let op0 := vertical_intersection_point p (low c) in 
                    match op0 with 
                       | None => [::]
                       | Some(p0) =>
                        Bcell  ((no_dup_seq ([:: p0; p]))++(pts c)) (low c) (high c) :: (closing_rest p q)
                    end
    end.

(* at each step we create the cell under the first outgoing edge and when there's only one left,
we create the two last cells *)
Fixpoint opening_cells (p : pt) (out : seq edge) (low_e : edge) (high_e : edge) : (seq cell) :=

      match out with
    | [::] => let op0 := vertical_intersection_point p low_e in 
              let op1 := vertical_intersection_point p high_e in
                      match (op0,op1) with 
                          |(None,_) |(_,None)=> [::]
                          |(Some(p0),Some(p1)) =>
                              (Bcell  (no_dup_seq ([:: p1; p; p0])) low_e high_e) ::[::]
                      end
    
    | [:: only_out] =>  let op0 := vertical_intersection_point p low_e in 
                      let op1 := vertical_intersection_point p high_e in
                      match (op0,op1) with 
                          |(None,_) |(_,None)=> [::]
                          |(Some(p0),Some(p1)) =>
                                (Bcell  (no_dup_seq ([:: p; p0])) low_e only_out)::(Bcell  (no_dup_seq ([:: p1; p])) only_out high_e)::[::]
                            end

    | c::q => let op0 := vertical_intersection_point p low_e in 
                    match op0 with 
                       | None => [::]
                       | Some(p0) =>
                        (Bcell  (no_dup_seq([:: p; p0])) low_e c) :: opening_cells p q c high_e
                    end
end.


Fixpoint extract_h (cells : seq cell) : edge :=
  match cells with 
   [::] => dummy_edge
   | [:: last_cell] => high last_cell
   | c::q => extract_h q
  end.

Definition extract_l_h_edges (cells : seq cell) : edge * edge :=
  match cells with
    | [::] => (dummy_edge, dummy_edge)
    | [:: only_cell] => (low only_cell, high only_cell)
    | c::q => (low c, extract_h q)
end.

Fixpoint insert_open (open_cells : seq cell) (new_open_cells : seq cell) (low_e : edge) : seq cell :=
  match open_cells with 
    | [::] => new_open_cells
    | c::q => if ((high c) == low_e) then c::(new_open_cells ++ q) else c::(insert_open q new_open_cells low_e)
  end.

Definition insert_open_cell_2 (first_cells : seq cell) (new_open_cells : seq cell) (last: seq cell) : seq cell :=
 first_cells++new_open_cells++last.

Fixpoint insert_open_cell (open_cells : seq cell) (new_open_cells : seq cell) (last: seq cell) : seq cell :=
  match open_cells with 
    | [::] => new_open_cells
    | c::q => if (contains last c) then c::(new_open_cells ++ q) else c::(insert_open_cell q new_open_cells last)
  end.

Fixpoint open_cells_decomposition_fix open_cells pt first_cells contact last_cells : seq cell * seq cell * seq cell :=
  match open_cells with
    | [::] => (first_cells, contact, last_cells)
    | Bcell lpt low high :: q  => if (contains_point pt (Bcell lpt low high)) then 
                                 open_cells_decomposition_fix q pt first_cells (contact++[::Bcell lpt low high]) last_cells
                                 else if (point_under_edge pt low) then
                                          open_cells_decomposition_fix q pt first_cells contact (last_cells++[::Bcell lpt low high])
                                      else open_cells_decomposition_fix q pt (first_cells++([::Bcell lpt low high])) contact last_cells
    end.

Definition open_cells_decomposition (open_cells : seq cell) (p : pt) : seq cell * seq cell * seq cell :=
  match open_cells with
    | [::] => ([::],[::],[::])
    | _  => open_cells_decomposition_fix open_cells p [::] [::] [::]
  end.

Fixpoint extract_last_cell (open_cells : seq cell) (contact_cells : seq cell) : seq cell  :=
  match open_cells with
    | [::] => [::]
    | c::q => if (contains contact_cells c) then [:: c] else extract_last_cell q contact_cells 
  end.


Definition step (e : event) (open_cells : seq cell) (closed_cells : seq cell) : (seq cell) * (seq cell) :=
   let p := point e in
   let '(first_cells, contact_cells, last_cells) := open_cells_decomposition open_cells p in
   let (lower_edge, higher_edge) := extract_l_h_edges contact_cells in 
   let closed := closing_cells p contact_cells in 
   let closed_cells := closed_cells++closed in
   let new_open_cells := opening_cells p (outgoing e) lower_edge higher_edge in
   ((insert_open_cell_2 first_cells new_open_cells last_cells), closed_cells).

Definition event_close_edge ed ev : bool :=
ed \in incoming ev.

Definition end_edge edge events : bool :=
has (event_close_edge edge) events.

Definition close_alive_edges open future_events : bool := 
all (fun c => (end_edge (low c) future_events) && (end_edge (high c) future_events)) open.

Fixpoint close_edges_from_events events : bool :=
  match events with
  | [::] => true
  | Bevent pt inc out ::future_events => all (fun edge => end_edge edge future_events) out && close_edges_from_events future_events
  end.

Lemma insert_opening_closeness open_cells new_open_cells last_cells events : 
  close_alive_edges open_cells events -> close_alive_edges new_open_cells events ->
  close_alive_edges last_cells events -> close_alive_edges (insert_open_cell open_cells new_open_cells last_cells) events.
Proof.
elim open_cells => [//= | c open Ih] .
move => C_open.
rewrite /close_alive_edges in C_open.
move => /allP in C_open.
have  : (close_alive_edges open events).
rewrite /close_alive_edges.
apply /allP.
Admitted.

    

  

  
  

  


Lemma step_keeps_closeness open closed current_event (future_events : seq event) : 
close_alive_edges open (current_event::future_events) && close_edges_from_events (current_event::future_events) ->
close_alive_edges  (step current_event open closed).1  future_events.
Proof.

rewrite /close_alive_edges.
rewrite /event_close_edge .
intros H .

rewrite /step.
case H1 : (extract_l_h_edges
[seq x <- open | contains_point (point current_event) x]) => [lower_edge higher_edge].

(*case H1 : (step current_event open closed) => [open2 dummy].*)
apply /allP.
move => c0 c0in2.
apply /andP.
split.
Search ((_,_).1).

Admitted.

Fixpoint adjacent_cells_aux open b: bool :=
  match open with
  | [::] => true
  | a::q => (high b == low a) && adjacent_cells_aux q a
  end.

Definition adjacent_cells open : bool :=
  match open with 
  | [::] => true
  | b::q => adjacent_cells_aux q b
  end.

(* toutes les arêtes présentes dans la liste des événements qui sont déjà vivantes sont dans la liste des cellules 
   car dans un second temps la liste des cellules qu'on obtient à la fin doit contenir toutes les arêtes
   après un certain événement 
   il faut vérifier que on ouvre pour une certaine hauteur tout ce qu'on ferme.

*)

Lemma step_keeps_adjacent open closed current_event (future_events : seq event) :
adjacent_cells open -> let (open2, _) := step current_event open closed in adjacent_cells open2.
rewrite /adjacent_cells.
elim : open =>[ /= It| head q Ih /=].

set opened  := opening_cells (point current_event) (outgoing current_event) dummy_edge dummy_edge.
 case : opened => [//=|head q /=].
Admitted.

Lemma opening_cells_eq  p out low_e high_e:
  opening_cells   p out low_e high_e =
      match out with
    | [::] => let op0 := vertical_intersection_point p low_e in 
              let op1 := vertical_intersection_point p high_e in
                      match (op0,op1) with 
                          |(None,_) |(_,None)=> [::]
                          |(Some(p0),Some(p1)) =>
                              (Bcell  (no_dup_seq ([:: p1; p; p0])) low_e high_e) ::[::]
                      end
    
    | only_out::[::] =>  let op0 := vertical_intersection_point p low_e in 
                      let op1 := vertical_intersection_point p high_e in
                      match (op0,op1) with 
                          |(None,_) |(_,None)=> [::]
                          |(Some(p0),Some(p1)) =>
                                (Bcell  (no_dup_seq ([:: p; p0])) low_e only_out)::(Bcell  (no_dup_seq ([:: p1; p])) only_out high_e)::[::]
                            end

    | c::q => let op0 := vertical_intersection_point p low_e in 
                    match op0 with 
                       | None => [::]
                       | Some(p0) =>
                        (Bcell  (no_dup_seq([:: p; p0])) low_e c) :: opening_cells p q c high_e
                    end
end.
Proof. by case: out. Qed.

Lemma size_open_ok (p : pt) (out : seq edge) (low_e : edge) (high_e : edge) :   
let open :=  opening_cells p out low_e high_e in  
(size open = size out + 1)%N. 
 Proof.
rewrite /opening_cells_eq.
rewrite opening_cells_eq.
elim :out =>[ /=|op0 op1 Ih /=].
case : (vertical_intersection_point p low_e) .
case : (vertical_intersection_point p high_e).
Admitted.

Lemma step_size_close (e : event) (open : seq cell) (closed : seq cell) :   
let (open2, close2) := step e open closed in  
(size close2 = size closed + size (outgoing e) + 1)%N. 
 Proof.
rewrite /step.

Admitted.


(* Lemma step_size_open (e : event) (open : seq cell) (closed : seq cell) :   *)
(*    let (open2, close2) := step e open closed in (size open2 = size open - size (incoming e) + size (outgoing e))%N. *)
(* Admitted. *)




Fixpoint scan (events : seq event) (open_cells : seq cell) (closed_cells : seq cell) : seq cell :=
   match events with 
      | [::] => closed_cells
      | e::q => let (open, closed) := (step e open_cells closed_cells) in  scan q open closed
 end.


Definition get_high_low x low high : rat * rat :=
if x < low then (x, high) else if high < x then (low, x) else (low, high).

(*
Fixpoint search_l_h_edges (events : seq event) (low_x : rat) (high_x : rat) (low_y : rat) (high_y : rat) (proof : low_x < high_x): edge*edge :=
  match events with
  | [::] => (@Bedge (Bpt (low_x - 1%:Q) (low_y - 1%:Q)) (Bpt (high_x + 1%:Q) (low_y - 1%:Q)) _, @Bedge (Bpt (low_x - 1%:Q) (high_y + 1%:Q)) (Bpt (high_x + 1%:Q) (high_y + 1%:Q)) _)
  | e::q => let p := point e in
            let (lowx, highx) := get_high_low (p_x p) low_x high_x in
            let (lowy, highy) := get_high_low (p_y p) low_y high_y in
            search_l_h_edges q lowx highx lowy highy _
  end.

Definition generate_outer_box (events : seq event) : edge * edge :=
  match events with
  | [::] => (dummy_edge,dummy_edge)
  | e::q => let p := point e in search_l_h_edges q (p_x p) ((p_x p) +1%:Q) (p_y p) (p_y p) _ 
  end.

*)

Definition start (events : seq event) (bottom : edge) (top : edge): seq cell :=
    match events with
      | [::] => [::]
      | e :: q => 
          let p := point e in let out := outgoing e in
           scan q (opening_cells p out bottom top) [::]
      end. 
(*
Definition events_inside_bottom_top events bottom top : Prop := 
  (p_x (left_pt bottom) = p_x (left_pt top)) && (p_x (left_pt bottom) = p_x (left_pt top))
*)
Definition lexPtEv (e1 e2 : event) : bool :=
  let p1 := point e1 in let p2 := point e2 in
  (p_x p1 < p_x p2) || ((p_x p1 == p_x p2) && (p_y p1 < p_y p2)).


Lemma add_event_preserve_first p e inc ev evs :
  (0 < size (add_event p e inc (ev :: evs)))%N /\
  (point (head ev (add_event p e inc (ev :: evs))) = p \/
   point (head ev (add_event p e inc (ev :: evs))) = point ev).
Proof.
rewrite /=.
case: ev => [p1 i1 o1].
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
  by case: inc {Ih}=> /=; (apply/andP; split=> //); rewrite /lexPtEv /= pltp1.
have [/eqP pp1 | pnp1'] /= := boolP (p_x p == p_x (point ev1)).
  have pyneq : p_y p != p_y (point ev1).
    apply/eqP=> pp1'; case pnp1.
    move: p (point ev1) {pnp1 Ih pnltp1} pp1 pp1'.
    by move=> [a b][c d] /= -> ->.
  have [ pltp1 | pnltp1'] /= := boolP(p_y p < p_y (point ev1)).
    by case: (inc); rewrite /= path_evs andbT /lexPtEv /= pp1 eqxx pltp1 orbT.
  have p1ltp : p_y (point ev1) < p_y p.
    by rewrite ltNge le_eqVlt negb_or pyneq pnltp1'.
  case evseq : evs => [ | [p2 i2 o2] evs2].
    by case: (inc)=> /=; rewrite /lexPtEv /= pp1 eqxx p1ltp orbT.
  rewrite -evseq.
  case aeq : (add_event p e inc evs) => [ | e' evs3].
    have := add_event_preserve_first p e inc
           {| point := p2; incoming:= i2; outgoing := o2 |} evs2.
      by rewrite -evseq aeq => [[]].
  case: (add_event_preserve_first p e inc
         {| point := p2; incoming:= i2; outgoing := o2 |} evs2)=> _.
  rewrite -evseq aeq /= => [] [eqp | eqp2].
    apply/andP; split; last by move: Ih; rewrite aeq.
    by rewrite /lexPtEv eqp pp1 eqxx p1ltp orbT.
  apply/andP; split; last by move: Ih; rewrite aeq.
  move: path_evs; rewrite evseq /= andbC => /andP[] _.
  by rewrite /lexPtEv /= eqp2.
have p1ltp : p_x (point ev1) < p_x p.
  by rewrite ltNge le_eqVlt negb_or pnp1' pnltp1.
case evseq : evs => [ | [p2 i2 o2] evs2].
  by case: (inc)=> /=; rewrite /lexPtEv /= p1ltp.
case aeq : (add_event p e inc evs) => [ | e' evs3].
  case: (add_event_preserve_first p e inc
       {| point := p2; incoming:= i2; outgoing := o2 |} evs2).
  by rewrite -evseq aeq.
case: (add_event_preserve_first p e inc
     {| point := p2; incoming:= i2; outgoing := o2 |} evs2) => _.
have path_e'evs3 : path lexPtEv e' evs3 by move: Ih; rewrite aeq.
rewrite -evseq aeq /= => [][e'p | e'p2]; rewrite path_e'evs3 andbT.
  by rewrite /lexPtEv e'p p1ltp.
by move: path_evs; rewrite evseq /= andbC /lexPtEv e'p2=> /andP[].
Qed.

