
From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

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

Record cell := Bcell  {left_pts : list pt; right_pts : list pt; low : edge; high : edge}.

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
  pue_formula p (left_pt e) (right_pt e) <= 0.

  (* returns true if p is strictly under e *)
Definition point_strictly_under_edge (p : pt) (e : edge) : bool :=
  pue_formula p (left_pt e) (right_pt e) < 0.

Notation "p '<<=' e" := (point_under_edge p e)( at level 70, no associativity).
Notation "p '<<<' e" := (point_strictly_under_edge p e)(at level 70, no associativity).


(*returns true if e1 is under e2*)

Definition compare_incoming (e1 e2 : edge) : bool :=
  let: Bedge a _ _ := e1 in
   a <<= e2.

(*returns true if e1 is under e2*)
Definition compare_outgoing (e1 e2 : edge) : bool :=
  let: Bedge _ b _ := e1 in
   b <<= e2.



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

Variable R : numFieldType.
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

Lemma pue_f_eq p_x p_y a_x a_y : 
pue_f p_x p_y p_x p_y a_x a_y == 0.
Proof.
rewrite /pue_f /=.

apply /eqP.
mc_ring.
Qed.

Lemma pue_f_two_points p_x p_y a_x a_y : 
pue_f p_x p_y p_x p_y a_x a_y == 0 /\ pue_f p_x p_y a_x a_y p_x p_y == 0 /\
pue_f p_x p_y a_x a_y a_x a_y == 0.
Proof.
split.
apply pue_f_eq.
split.
have := pue_f_c p_x p_y  a_x a_y p_x p_y.
move => ->.
apply pue_f_eq.
have := pue_f_c  a_x a_y  a_x a_y p_x p_y.
move => <-.
apply pue_f_eq.
Qed.

Lemma pue_f_vert p_y a_x a_y b_x b_y : 
 (pue_f  a_x a_y b_x b_y b_x p_y) == (b_x - a_x) * (p_y - b_y).
Proof.
rewrite /pue_f.
apply /eqP.
mc_ring.
Qed.


Lemma ax4 p_x p_y q_x q_y r_x r_y t_x t_y : 
pue_f t_x t_y q_x q_y r_x r_y + pue_f p_x p_y t_x t_y r_x r_y
+ pue_f p_x p_y q_x q_y t_x t_y == pue_f p_x p_y q_x q_y r_x r_y.
Proof.
rewrite /pue_f.
apply /eqP.
  mc_ring.
Qed.

Lemma pue_f_linear l a b c d e f :
l * pue_f a b c d e f = pue_f a (l*b) c (l*d) e (l*f).
Proof.
rewrite /pue_f.
mc_ring.
Qed.

Lemma pue_f_on_edge_y a_x a_y b_x b_y m_x m_y :
pue_f a_x a_y b_x b_y m_x m_y == 0 ->
(b_x - a_x) * m_y = m_x * (b_y -a_y)- (a_x * b_y - b_x *a_y).
Proof.
move => /eqP abmeq0.
apply /eqP.
rewrite -subr_eq0.
apply /eqP.
rewrite -abmeq0 /pue_f.
mc_ring.
Qed.

Lemma pue_f_on_edge a_x a_y b_x b_y c_x c_y d_x d_y m_x m_y :
pue_f a_x a_y b_x b_y m_x m_y == 0 -> 
(b_x - a_x) * pue_f c_x c_y d_x d_y m_x m_y == 
(m_x - a_x) * pue_f c_x c_y d_x d_y b_x b_y + (b_x - m_x) * pue_f c_x c_y d_x d_y a_x a_y.
Proof.
move => on_ed.
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_triangle_on_edge a_x a_y b_x b_y p_x p_y p'_y :
pue_f a_x a_y b_x b_y p_x p'_y == 0 -> 
(b_x - a_x) * pue_f a_x a_y p_x p_y p_x p'_y == 
(p_x - a_x) * pue_f a_x a_y p_x p_y b_x b_y .
Proof.
move => on_ed .
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_triangle_on_edge' a_x a_y b_x b_y p_x p_y p'_y :
pue_f a_x a_y b_x b_y p_x p'_y == 0 -> 
(b_x - a_x) * pue_f p_x p_y b_x b_y p_x p'_y == 
(b_x - p_x) * pue_f a_x a_y p_x p_y b_x b_y .
Proof.
move => on_ed .
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.


Lemma pue_f_on_edge_same_point_counter_example :
  ~ (forall a_x a_y b_x b_y p_x p_y p_x' p_y',
    a_x != b_x ->  (* The two points are not on the same vertical *)
    pue_f a_x a_y b_x b_y p_x p_y == 0 -> 
    pue_f a_x a_y b_x b_y p_x' p_y' == 0 ->
    (p_y == p_y') = (p_x == p_x')).
Proof.
move=> bad_thm.
have := bad_thm 1%:R 0 2%:R 0 1%:R 0 2%:R 0.
rewrite (eqr_nat R 1%N 2%N) /=.
have -> : pue_f 1%:R 0 2%:R 0 1%:R 0 == 0.
  apply/eqP; rewrite /pue_f.
  mc_ring.
have -> : pue_f 1%:R 0 2%:R 0 2%:R 0 == 0.
  apply/eqP; rewrite /pue_f.
  mc_ring.
move=> /(_ isT isT isT).
rewrite eqxx.
by[].
Qed.

Lemma pue_f_on_edge_same_point a_x a_y b_x b_y p_x p_y p_x' p_y': 
a_x != b_x ->
pue_f a_x a_y b_x b_y p_x p_y == 0 -> 
pue_f a_x a_y b_x b_y p_x' p_y' == 0 ->
(p_x == p_x') -> (p_y == p_y').
Proof.
move => axnbx puep0 puep'0.
have pyeq := (pue_f_on_edge_y puep0 ).
have p'yeq := (pue_f_on_edge_y puep'0 ).
move=> xxs; have yys : (b_x - a_x) * p_y = (b_x - a_x) * p_y'.
  by rewrite pyeq (eqP xxs) p'yeq.
move: (axnbx); rewrite eq_sym -subr_eq0=> bxmax.
apply/eqP.
by apply: (mulfI bxmax).
Qed.
  
Lemma pue_f_ax5 p_x p_y q_x q_y a_x a_y b_x b_y c_x c_y :
  pue_f p_x p_y a_x a_y b_x b_y *
  pue_f p_x p_y q_x q_y c_x c_y +
  pue_f p_x p_y b_x b_y c_x c_y *
  pue_f p_x p_y q_x q_y a_x a_y =
  pue_f p_x p_y a_x a_y c_x c_y *
  pue_f p_x p_y q_x q_y b_x b_y.
Proof.
rewrite /pue_f; mc_ring.
Qed.

End ring_sandbox.

Lemma pue_formulaE a b c : pue_formula a b c =
   pue_f (p_x a) (p_y a) (p_x b) (p_y b) (p_x c) (p_y c). 
Proof. by case: a b c=> [a_x a_y] [b_x b_y] [c_x c_y]. Qed.

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

Lemma pue_formula_vert a b c : (p_x b = p_x c) ->  
pue_formula a b c == (p_x b - p_x a) * (p_y c - p_y b).
Proof.
move: a b c => [ax ay] [b_x b_y] [cx cy]/= <-.
apply : pue_f_vert.
Qed.

Lemma ax4_three_triangles p q r t : 
pue_formula t q r + pue_formula p t r + pue_formula p q t 
== pue_formula p q r.
Proof.
move : p q r t => [px py] [q_x q_y] [rx ry] [t_x t_y]/= .
apply : ax4.
Qed.


Lemma pue_formula_two_points a b : 
pue_formula a a b == 0 /\ pue_formula a b a == 0 /\
pue_formula a b b == 0.
Proof.
move : a b => [ax ay] [b_x b_y] /=.
apply pue_f_two_points.
Qed.

Lemma pue_formula_on_edge a b c d m :
pue_formula a b m == 0 ->  
(p_x b - p_x a) * pue_formula c d m == 
(p_x m - p_x a) * pue_formula c d b + (p_x b - p_x m) * pue_formula c d a.
Proof.
move : a b c d m => [ax ay] [b_x b_y] [cx cy] [dx dy] [mx my]/=.
apply pue_f_on_edge.
Qed.

Lemma pue_formula_on_edge_y a b m :
pue_formula a b m == 0 ->
(p_x b - p_x a) * p_y m = p_x m * (p_y b - p_y a) - (p_x a * p_y b - p_x b * p_y a).
Proof.
move : a b m => [ax ay] [b_x b_y]  [mx my]/=.
apply pue_f_on_edge_y.
Qed.

Lemma pue_formula_triangle_on_edge a b p p' :
p_x p = p_x p' -> pue_formula a b p' == 0 ->
(p_x b - p_x a) * pue_formula a p p' == 
(p_x p - p_x a) * pue_formula a p b.
Proof.
move : a b p p' => [ax ay] [b_x b_y] [px py] [p'x p'y] /=.
move => <-.
apply pue_f_triangle_on_edge.
Qed.

Lemma pue_formula_triangle_on_edge' a b p p' :
p_x p = p_x p' -> pue_formula a b p' == 0 ->
(p_x b - p_x a) * pue_formula p b p' == 
(p_x b - p_x p) * pue_formula a p b.
Proof.
move : a b p p' => [ax ay] [b_x b_y] [px py] [p'x p'y] /=.
move => <-.
apply pue_f_triangle_on_edge'.
Qed.

Definition subpoint (p : pt) :=
  {| p_x := p_x p; p_y := p_y p - 1 |}.

Lemma point_sub_right (p a : pt) :
  (p_x p < p_x a) -> 0 < pue_formula p (subpoint p) a.
Proof.
case : p=> [px py]; case: a => [ax ay] /=.
move=> agtp; rewrite !mulrBr !mulr1 !opprD !opprK !addrA subrK.
rewrite !(addrAC _ _ (-(ax * py))) addrN add0r.
by rewrite (addrAC _ _ (px * ay)) addNr add0r addrC subr_gt0.
Qed.

Lemma underW p e :
  (p <<< e) ->
  (p <<= e).
Proof.
rewrite /point_under_edge /point_strictly_under_edge.
apply : ltW .
Qed.

Lemma underWC p e : 
~  p <<= e ->
~ (p <<< e).
Proof.
apply : (contra_not  (p <<= e) (p <<< e)).
apply : underW.
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

Definition valid_edge e p := (p_x (left_pt e) <= p_x p) && (p_x p <= p_x (right_pt e)).
Definition valid_cell c x := (valid_edge (low c) x) /\ (valid_edge (high c) x).


Definition point_on_edge (p: pt) (e :edge) : bool :=
  (pue_formula p (left_pt e) (right_pt e) == 0) && (valid_edge e p).

Notation "p '===' e" := (point_on_edge p e)( at level 70, no associativity).

Definition edge_below (e1 : edge) (e2 : edge) : bool :=
((left_pt e1 <<= e2) && (right_pt e1 <<= e2))
|| (~~  (left_pt e2 <<< e1) && ~~ (right_pt e2<<< e1)).

Notation "e1 '<|' e2" := (edge_below e1 e2)( at level 70, no associativity).

Definition right_form (c : cell) : bool :=
  (low c) <| (high c).

Lemma left_on_edge e :
(left_pt e) === e.
Proof.
move : e => [ l r inE].
rewrite /point_on_edge //=.
have := pue_formula_two_points l r.
move => [] ->  _ /=.
apply  /andP .
split.
  by [].
rewrite /=.
by apply ltW.
Qed.

Lemma right_on_edge e :
(right_pt e) === e.
Proof.
move : e => [ l r inE].
rewrite /point_on_edge //=.
have := pue_formula_two_points r l.
move => [] _ [] -> _ /=.
apply  /andP .
split.
  rewrite /=.
  by apply ltW.
by [].
Qed.


Lemma point_on_edge_above low_e high_e a : 
a === high_e ->
~~  (left_pt high_e <<< low_e) ->
~~ (right_pt high_e <<< low_e) ->
~~ (a <<< low_e).
Proof.
move : high_e => [lr hr inH] /=.

rewrite /point_on_edge /valid_edge => /andP [] /= poea /andP [] linfa ainfr.

have pf := pue_formula_on_edge (left_pt low_e) (right_pt low_e) poea.
rewrite /point_strictly_under_edge -!leNgt.
rewrite -pue_formula_cycle => llrllh.
rewrite -pue_formula_cycle => llrllrh.
have diffa : (p_x lr - p_x a) <= 0.
  by rewrite subr_cp0.
have diffb : (p_x hr - p_x a) >= 0.
  by rewrite subr_cp0.
have difflh : (p_x lr - p_x hr) < 0.
  by rewrite subr_cp0.
rewrite -pue_formula_cycle -( ler_nmul2l difflh _ 0) mulr0.
move : pf.
rewrite [x in _ == x] addrC -subr_eq => /eqP <-.
rewrite -oppr_ge0 opprD /= addr_ge0//.
  by rewrite -mulNr mulr_ge0 // oppr_ge0.
by rewrite opprK mulr_ge0.
Qed.


Lemma point_on_edge_under low_e high_e a : 
a === (low_e) ->
 (left_pt low_e) <<= high_e ->
 (right_pt low_e) <<= high_e ->
  a <<= high_e.
Proof.
move : low_e => [lr hr inH] /=.

rewrite /point_on_edge /valid_edge => /andP [] /= poea /andP [] linfa ainfr.

have pf := pue_formula_on_edge (left_pt high_e) (right_pt high_e) poea.
rewrite /point_under_edge .
rewrite -pue_formula_cycle => /= llrllh.
rewrite -pue_formula_cycle => /= llrllrh.
have diffa : (p_x lr - p_x a) <= 0.
  by rewrite subr_cp0.
have diffb : (p_x hr - p_x a) >= 0.
  by rewrite subr_cp0.
have difflh : (p_x lr - p_x hr) < 0.
  by rewrite subr_cp0.
rewrite -pue_formula_cycle -( ler_nmul2r difflh 0 _ ) mul0r mulrC.
move : pf.
rewrite [x in _ == x] addrC -subr_eq => /eqP <-.
rewrite   /= addr_ge0//.
   by rewrite mulr_le0 .
rewrite -mulNr mulr_le0 // oppr_le0.
by rewrite subr_cp0.
Qed.

Lemma not_strictly_above' low_e high_e p': 
~~ (left_pt (high_e) <<< low_e) ->
~~ (right_pt (high_e) <<< low_e) ->
p' ===  high_e ->  p_x (right_pt (low_e)) = p_x p'  ->
right_pt (low_e) <<= high_e .
Proof.
move : low_e => [ll lr inL] /=.
move => pablh pabrh poep' eqxp'p.
have /= /eqP puefcpp' := pue_formula_vert (left_pt (Bedge inL)) eqxp'p .
have := (point_on_edge_above poep' pablh pabrh ).
rewrite /point_strictly_under_edge  -pue_formula_cycle -leNgt puefcpp' /point_under_edge.
have inle: (p_x lr - p_x ll) >0.
  by rewrite subr_cp0.
rewrite (pmulr_rge0 _ inle) => inp'lr.
have :=  (ax4_three_triangles lr  (left_pt high_e) (right_pt high_e) p') => /eqP <-.
move : poep'.
rewrite /point_on_edge=> /andP [] /eqP pue0 valp'.
rewrite pue0.
have := (pue_formula_vert (right_pt high_e) eqxp'p  ).
rewrite -pue_formula_cycle eqxp'p => /eqP ->.
move : valp'.
rewrite /valid_edge => /andP [] xlhp' xrhp'.
have xrhp'0: p_x p' - p_x (right_pt high_e) <=0.
  by rewrite subr_cp0.
rewrite add0r.
rewrite -oppr_ge0 opprD /= addr_ge0//.
  by rewrite -mulNr mulr_ge0 // oppr_ge0.
have := (pue_formula_vert (left_pt high_e) eqxp'p  ).
rewrite -pue_formula_opposite pue_formula_cycle eqxp'p => /eqP ->.
have xlhp'0: p_x p' - p_x (left_pt high_e) >= 0.
  by rewrite subr_cp0.
by rewrite  mulr_ge0.
Qed.

(* returns the point of the intersection between a vertical edge
 intersecting p and the edge e if it exists, None if it doesn't *)

Definition vertical_intersection_point (p : pt) (e : edge) : option pt := 

  if valid_edge e p then Some(Bpt (p_x p) (((p_x p) - p_x (left_pt e))
   * (((p_y (right_pt e)) - p_y (left_pt e)) /
    ((p_x (right_pt e)) - p_x (left_pt e))) + p_y (left_pt e)))
    else None.

Lemma vertical_none p e :
  ~~ valid_edge e p -> vertical_intersection_point p e = None.
Proof.
move: p e => [px py] [[ax ay] [b_x b_y] ab] h /=.
rewrite /vertical_intersection_point /=.
by rewrite (negbTE h).
Qed.


Lemma vertical_correct p e : 
    match(vertical_intersection_point p e) with None => ~~ valid_edge e p | Some(i) => i === e end.
Proof.
move: p e => [ptx pty] [[ax ay] [bx b_y]  /=ab] .
rewrite /vertical_intersection_point.
case : ifP => /= h ; last first.
by [].
have: ax != bx.
rewrite neq_lt ab //=.
rewrite /pue_formula.
set py := ((b_y - ay) / (bx - ax) * ptx + (ay - (b_y - ay) / (bx - ax) * ax)).
move => h2.
rewrite /point_on_edge .
apply /andP.
split; last first.
exact h.
apply pue_f_inters.
by apply /eqP /nesym /eqP .
by [].
Qed.



Lemma exists_point_valid e p :
(valid_edge e p) -> 
exists p', vertical_intersection_point p e = Some (p').
Proof.
have := vertical_correct p e.
case : (vertical_intersection_point p e)=> [vp |//=].
  rewrite /point_on_edge.
  move => a b.
  by exists vp.
move => a b.
exists p.
by rewrite b in a.
Qed.

Lemma intersection_on_edge e p p' :
vertical_intersection_point p e = Some (p') ->
p'=== e /\ p_x p = p_x p'.
Proof.
have := vertical_correct p e.
case vert : (vertical_intersection_point p e)=> [vp |//=].
move: vert.
rewrite /vertical_intersection_point.
case : (valid_edge e p) => [| //].
move => [] /= vpq  poe [].
move => <-. 
by rewrite poe -vpq /=.
Qed.

Lemma not_strictly_under' low_e high_e p' : 
(left_pt (low_e)) <<= (high_e) ->
(right_pt (low_e))<<= (high_e) ->
(* This is an alternative way to say
  valid_edge low_e (right_pt high_e) *)
p' === low_e ->  p_x (right_pt (high_e)) = p_x p'  ->
~~ (right_pt (high_e) <<< low_e).
Proof.
move : high_e => [hl hr inH] /=.
move => pablh pabrh poep' eqxp'p.
have /= /eqP puefcpp' := pue_formula_vert (left_pt (Bedge inH)) eqxp'p .
have := (point_on_edge_under poep' pablh pabrh ).
rewrite /point_under_edge  -pue_formula_cycle -leNgt puefcpp'.
have inle: (p_x hr - p_x hl) >0.
  by rewrite subr_cp0.
rewrite (pmulr_rle0 _ inle )  => inp'hr.
have :=  (ax4_three_triangles hr  (left_pt low_e) (right_pt low_e) p') => /eqP <-.
move : poep'.
rewrite /point_on_edge=> /andP [] /eqP pue0 valp'.
rewrite pue0.
have := (pue_formula_vert (right_pt low_e) eqxp'p  ).
rewrite -pue_formula_cycle eqxp'p => /eqP ->.
move : valp'.
rewrite /valid_edge => /andP [] xlhp' xrhp'.
have xrhp'0: p_x p' - p_x (right_pt low_e) <=0.
  by rewrite subr_cp0.
rewrite add0r addr_ge0//.
  by rewrite mulr_le0.
have := (pue_formula_vert (left_pt low_e) eqxp'p  ).
rewrite pue_formula_opposite -pue_formula_cycle eqxp'p eqr_oppLR => /eqP ->.
by rewrite -mulNr mulr_le0 // oppr_le0 subr_cp0.
Qed.

Lemma pue_right_edge e p : 
p_x (right_pt e) == p_x p -> 
(p <<= e) = ((p_y p - p_y (right_pt e)) <= 0).
Proof.
move : e p  => [[ax ay][bx b_y] /= inE] [px py]  /=.
rewrite /point_under_edge /=.
move => /eqP <- /=.
have := (pue_f_vert py ax ay bx b_y).
rewrite pue_f_c /pue_f.
move => /eqP ->.
rewrite -subr_cp0 -opprB oppr_lt0 in inE.
by rewrite (pmulr_rle0 _  inE  ) .
Qed.

Lemma pue_left_edge e p : 
p_x (left_pt e) == p_x p -> 
(p <<= e) = (0 <= (p_y (left_pt e) - p_y p )).
Proof.
move : e p  => [[ax ay][bx b_y] /= inE] [px py]  /=.
rewrite /point_under_edge /=.
move => /eqP <- /=.
have := (pue_f_vert ay bx b_y ax py).
rewrite -pue_f_c /pue_f.
move => /eqP ->.
rewrite -subr_cp0 in inE.
by rewrite (nmulr_rle0 _  inE  ) .
Qed.

Lemma not_strictly_under low_e high_e  : 
(left_pt low_e) <<= high_e ->
(right_pt low_e) <<= high_e ->
valid_edge low_e (right_pt high_e)  ->
~~ (right_pt high_e <<< low_e).
Proof.
move => pableft pabright valright.
have  := exists_point_valid valright.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx.
apply :  not_strictly_under' pableft pabright poep' eqx.
Qed.

Lemma not_strictly_above low_e high_e : 
~~ (left_pt high_e <<< low_e) ->
~~ (right_pt high_e <<< low_e) ->
valid_edge (high_e) (right_pt (low_e)) ->
right_pt (low_e) <<= high_e.
Proof.
move => pableft pabright valright.
have  := exists_point_valid valright.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx.
apply :  not_strictly_above' pableft pabright poep' eqx.
Qed.

Lemma on_edge_same_point e p p': 
p === e -> p' === e ->
(p_x p == p_x p') -> (p_y p == p_y p').
Proof.
move : e => [l r inE].
rewrite /point_on_edge /= => /andP [].
rewrite -pue_formula_cycle=> p0 _ /andP [].
rewrite -pue_formula_cycle=> p'0 _.
have dif : p_x l != p_x r.
  by apply/eqP=> abs; move: inE; rewrite abs ltxx.
move: l r p0 p'0 dif {inE}=> [a_x a_y][b_x b_y] p0 p'0 dif.
move: p p' p0 p'0 => [x y] [x' y'] puep0 puep'0.
rewrite /=; apply: (pue_f_on_edge_same_point dif puep0 puep'0).
Qed.

Lemma point_valid_under_imp_y_inf e p p' : 
p <<= e ->
p'=== e -> p_x p = p_x p'->
0 <= (p_y p' - p_y p).
Proof.
move : e => [l r inE] /=.
move => pue poep'.
have := poep'.
rewrite /point_on_edge /valid_edge /= =>  /andP [] p_on_edge_p'   /andP [] linfp pinfr eqx.
move : pue.
rewrite -pue_formula_cycle in p_on_edge_p'.
rewrite -eqx in linfp pinfr.
rewrite /point_under_edge /=.
have := (pue_formula_triangle_on_edge eqx (p_on_edge_p')).

have /eqP := (pue_formula_vert l eqx  ) => ->.
have inle: (p_x r - p_x l) >0.
  by rewrite subr_cp0.
move => /eqP a.
have pminusl : (0 <= p_x p - p_x l).
  by rewrite subr_cp0.
  rewrite pue_formula_opposite -pue_formula_cycle oppr_le0 => lprpos.
have := (mulr_ge0 pminusl lprpos).
rewrite -a.
rewrite (pmulr_rge0 _ inle).
case sup0 : (0 < (p_x p - p_x l)).
  by rewrite (pmulr_rge0 _ sup0).
move : sup0.
rewrite subr_cp0.
move => /negbT.
rewrite -leNgt => pinfl.
have : p_x p <= p_x l <= p_x p.
by rewrite linfp pinfl.
move => /le_anti eqxl.
have /= lone:= left_on_edge (Bedge inE).

move : lprpos.
rewrite pue_formula_opposite oppr_gte0 .
have /eqP -> := (pue_formula_vert r eqxl).
rewrite eqxl => yineq.
have inle2: (p_x l - p_x r) < 0.
by rewrite subr_cp0.

move => _.
rewrite (nmulr_rle0  _  inle2 ) in yineq.
have := (on_edge_same_point lone poep').
by rewrite -eqx eqxl => /(_ (eqxx _)) /eqP <-.
Qed.

Lemma point_valid_strict_under_imp_y_inf e p p' : 
p <<< e ->
p'=== e -> p_x p = p_x p'->
0 < (p_y p' - p_y p).
Proof.
move : e => [l r inE] /=.
move => pue poep'.
have := poep'.
rewrite /point_on_edge /valid_edge /= =>  /andP [] p_on_edge_p'   /andP [] linfp pinfeqr eqx.
move : pue.
rewrite -pue_formula_cycle in p_on_edge_p'.
rewrite -eqx in linfp pinfeqr.
rewrite /point_strictly_under_edge /=.
  have inle: (p_x r - p_x l) >0.
    by rewrite subr_cp0.
move: linfp; rewrite le_eqVlt=> /orP [/eqP lp | linfp].
  have : p_x p < p_x r by rewrite -lp.
  move=> { pinfeqr } pinfr.
  have := (pue_formula_triangle_on_edge' eqx (p_on_edge_p')).

  have /eqP := (pue_formula_vert r eqx  ); rewrite pue_formula_opposite.
  rewrite -pue_formula_cycle -[RHS]opprK => /oppr_inj ->.
  move => /eqP a.
  have rminusp : (0 < p_x r - p_x p).
    by rewrite subr_cp0.
  rewrite pue_formula_opposite -pue_formula_cycle oppr_lt0 => lprpos.
  have := (mulr_gt0 rminusp lprpos).
  rewrite -a.
  rewrite (pmulr_rgt0 _ inle).
  rewrite -mulNr opprB.
  by rewrite (pmulr_rgt0 _ rminusp).
have pminusl : 0 < p_x p - p_x l by rewrite subr_cp0.
have := (pue_formula_triangle_on_edge eqx (p_on_edge_p')).
have /eqP := (pue_formula_vert l eqx  )=> -> /eqP a.
rewrite pue_formula_opposite -pue_formula_cycle oppr_lt0=> lprpos.
have := mulr_gt0 pminusl lprpos.
rewrite -a.
by rewrite (pmulr_rgt0 _ inle) (pmulr_rgt0 _ pminusl).
Qed.

Lemma point_valid_above_imp_y_inf e p p' : 
~~ (p <<< e) ->
p' === e -> p_x p = p_x p'->
0 <= (p_y p - p_y p').
Proof.
move : e => [l r inE] /=.
move => pue poep'.
have := poep'.
rewrite /point_on_edge /valid_edge /= =>  /andP [] p_on_edge_p'   /andP [] linfp pinfr eqx.
move : pue.
rewrite -pue_formula_cycle in p_on_edge_p'.
rewrite -eqx in linfp pinfr.
rewrite /point_strictly_under_edge /=.
have := (pue_formula_triangle_on_edge eqx (p_on_edge_p')).

have /eqP := (pue_formula_vert l eqx  ) => ->.
have inle: (p_x r - p_x l) >0.
  by rewrite subr_cp0.
move => /eqP a.
have pminusl : (0 <= p_x p - p_x l).
  by rewrite subr_cp0.
  rewrite pue_formula_opposite -pue_formula_cycle oppr_lt0 -leNgt => lprpos.
have := mulr_ge0_le0 pminusl lprpos.
rewrite -a pmulr_rle0 //.

case sup0 : (0 < (p_x p - p_x l)).
  by rewrite (pmulr_rle0 _ sup0) !subr_cp0 .
move : sup0.
rewrite subr_cp0.
move => /negbT.
rewrite -leNgt => pinfl.
have : p_x p <= p_x l <= p_x p.
  by rewrite linfp pinfl.
move => /le_anti eqxl.
have /= lone:= left_on_edge (Bedge inE).

move : lprpos.
rewrite pue_formula_opposite oppr_le0.
have /eqP -> := (pue_formula_vert r eqxl).
rewrite eqxl => yineq.
have inle2: (p_x l - p_x r) < 0.
  by rewrite subr_cp0.

move => _.
rewrite (nmulr_rge0  _  inle2 ) subr_cp0 in yineq.
have := (on_edge_same_point lone poep').
by rewrite -eqx eqxl subr_cp0=> /(_ (eqxx _)) /eqP <-.
Qed.

Lemma under_low_imp_under_high low_e high_e p  : 
(left_pt low_e) <<= high_e ->
(right_pt low_e) <<= high_e ->
valid_edge low_e p ->
valid_edge high_e p ->
p <<= low_e -> p <<= high_e.
Proof.
move : low_e high_e => [ll lr inL] [hl hr inH]  /=.
move => pulh purh vallow valhigh.
have  := exists_point_valid vallow.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx'.
have  := exists_point_valid valhigh.
move => [] p'' vip' .
have  := intersection_on_edge vip' => [][] poep'' eqx''{vip' vip}.
have := poep''.
have := poep'.

rewrite /point_on_edge /valid_edge =>  /andP [] /= poepf' /andP []
 linfp' p'infr   /andP [] /= poepf'' /andP [] linfp'' p''infr.

rewrite -pue_formula_cycle in poepf'.
rewrite -eqx' in linfp' p'infr.
rewrite -eqx'' in linfp'' p''infr.
move => puep.


have ydiff := (point_valid_under_imp_y_inf puep poep' eqx').
rewrite eqx' in eqx''.
have puep' := (point_on_edge_under  poep' pulh purh).
have y'diff := (point_valid_under_imp_y_inf puep' poep'' eqx'').
rewrite subr_cp0 in ydiff.
rewrite subr_cp0 in y'diff.
have y''diff: (p_y p  <= p_y p'').
  by rewrite (le_trans  ydiff y'diff).
rewrite -eqx' in eqx''.
have := ax4_three_triangles p hl hr p''.
have /eqP pHleq :=  (pue_formula_vert hl eqx'').
have /eqP pHreq :=  (pue_formula_vert hr eqx'').
rewrite -pue_formula_cycle in pHreq.
rewrite pue_formula_opposite -pue_formula_cycle in pHleq.

move : poepf'' pHreq => /eqP ->  -> .
have :  pue_formula p hl p'' = - ((p_x p - p_x hl) * (p_y p'' - p_y p)).
  by rewrite -pHleq opprK.
move => ->.
rewrite add0r -mulrBl.
rewrite  [x in (x - _) * _ == _] addrC.
rewrite addrKA opprK.

rewrite /point_under_edge /= {pulh purh vallow valhigh poep' poep'' poepf' puep puep'}.
rewrite addrC.
rewrite -subr_cp0 in inH.
rewrite -subr_ge0 in y''diff.
move => /eqP <-.
by rewrite nmulr_rle0.
Qed.

Lemma under_low_imp_strict_under_high low_e high_e p  : 
(left_pt low_e) <<= high_e ->
(right_pt low_e) <<= high_e ->
valid_edge low_e p ->
valid_edge high_e p ->
p <<< low_e -> p <<< high_e.
Proof.
move : low_e high_e => [ll lr inL] [hl hr inH]  /=.
move => pulh purh vallow valhigh.
have  := exists_point_valid vallow.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx'.
have  := exists_point_valid valhigh.
move => [] p'' vip' .
have  := intersection_on_edge vip' => [][] poep'' eqx''{vip' vip}.
have := poep''.
have := poep'.

rewrite /point_on_edge /valid_edge =>  /andP [] /= poepf' /andP []
 linfp' p'infr   /andP [] /= poepf'' /andP [] linfp'' p''infr.

rewrite -pue_formula_cycle in poepf'.
rewrite -eqx' in linfp' p'infr.
rewrite -eqx'' in linfp'' p''infr.
move => puep.


have ydiff := (point_valid_strict_under_imp_y_inf puep poep' eqx').
rewrite eqx' in eqx''.
have puep' := (point_on_edge_under  poep' pulh purh).
have y'diff := (point_valid_under_imp_y_inf puep' poep'' eqx'').
rewrite subr_cp0 in ydiff.
rewrite subr_cp0 in y'diff.
have y''diff: (p_y p  < p_y p'').
  by rewrite (lt_le_trans  ydiff y'diff).
rewrite -eqx' in eqx''.
have := ax4_three_triangles p hl hr p''.
have /eqP pHleq :=  (pue_formula_vert hl eqx'').
have /eqP pHreq :=  (pue_formula_vert hr eqx'').
rewrite -pue_formula_cycle in pHreq.
rewrite pue_formula_opposite -pue_formula_cycle in pHleq.

move : poepf'' pHreq => /eqP ->  -> .
have :  pue_formula p hl p'' = - ((p_x p - p_x hl) * (p_y p'' - p_y p)).
  by rewrite -pHleq opprK.
move => ->.
rewrite add0r -mulrBl.
rewrite  [x in (x - _) * _ == _] addrC.
rewrite addrKA opprK.

rewrite /point_strictly_under_edge /= {pulh purh vallow valhigh poep' poep'' poepf' puep puep'}.
rewrite addrC.
rewrite -subr_cp0 in inH.
rewrite -subr_gt0 in y''diff.
move => /eqP <-.
by rewrite nmulr_rlt0.
Qed.

Lemma under_low_imp_under_high_bis low_e high_e p  : 
~~ (left_pt high_e <<< low_e) ->
~~ (right_pt high_e <<< low_e) ->
valid_edge low_e p ->
valid_edge high_e p ->
p <<= low_e -> p <<= high_e.
Proof.
move : low_e high_e => [ll lr inL] [hl hr inH]  .
move => pabhl pabhr vallow valhigh.
have  := exists_point_valid vallow.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx'.
have  := exists_point_valid valhigh.
move => [] p'' vip' .
have  := intersection_on_edge vip' => [][] poep'' eqx''{vip' vip}.
have := poep''.
have := poep'.

rewrite /point_on_edge /valid_edge =>  /andP [] /= poepf' /andP []
 linfp' p'infr   /andP [] /= poepf'' /andP [] linfp'' p''infr.

rewrite -pue_formula_cycle in poepf'.
rewrite -eqx' in linfp' p'infr.
rewrite -eqx'' in linfp'' p''infr.
move => /= puep.


have ydiff := (point_valid_under_imp_y_inf puep poep' eqx').
rewrite eqx' in eqx''.
symmetry in eqx''.
have pabp' := (point_on_edge_above  poep'' pabhl pabhr).
have a:= (point_valid_above_imp_y_inf _ _ _).
have y'diff := (point_valid_above_imp_y_inf pabp' poep' eqx'').
rewrite subr_cp0 in ydiff.
rewrite subr_cp0 in y'diff.
have y''diff: (p_y p  <= p_y p'').
  by rewrite (le_trans  ydiff y'diff).
rewrite -eqx' in eqx''.
have := ax4_three_triangles p hl hr p''.
have /eqP pHleq :=  (pue_formula_vert hl eqx'').
have /eqP pHreq :=  (pue_formula_vert hr eqx'').

rewrite pue_formula_opposite in pHreq.
rewrite pue_formula_cycle in pHleq.

move : poepf'' pHleq => /eqP  ->  -> .
have :  pue_formula p p'' hr = - ((p_x p'' - p_x hr) * (p_y p - p_y p'')).
  by rewrite -pHreq opprK.
move => ->.
rewrite add0r addrC -mulrBl.
rewrite  [x in (x - _) * _ == _] addrC.
rewrite addrKA opprK.

rewrite /point_under_edge /= {pabhl pabhr vallow valhigh poep' poep'' poepf' puep pabp'}.
rewrite addrC.
rewrite -subr_gte0 in inH.
rewrite -subr_le0 in y''diff.
move => /eqP <-.

by rewrite pmulr_rle0.
Qed.

Lemma under_low_imp_strict_under_high_bis low_e high_e p  : 
~~ (left_pt high_e <<< low_e) ->
~~ (right_pt high_e <<< low_e) ->
valid_edge low_e p ->
valid_edge high_e p ->
p <<< low_e -> p <<< high_e.
Proof.
move : low_e high_e => [ll lr inL] [hl hr inH]  .
move => pabhl pabhr vallow valhigh.
have  := exists_point_valid vallow.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx'.
have  := exists_point_valid valhigh.
move => [] p'' vip' .
have  := intersection_on_edge vip' => [][] poep'' eqx''{vip' vip}.
have := poep''.
have := poep'.

rewrite /point_on_edge /valid_edge =>  /andP [] /= poepf' /andP []
 linfp' p'infr   /andP [] /= poepf'' /andP [] linfp'' p''infr.

rewrite -pue_formula_cycle in poepf'.
rewrite -eqx' in linfp' p'infr.
rewrite -eqx'' in linfp'' p''infr.
move => /= puep.


have ydiff := (point_valid_strict_under_imp_y_inf puep poep' eqx').
rewrite eqx' in eqx''.
symmetry in eqx''.
have pabp' := (point_on_edge_above  poep'' pabhl pabhr).
have y'diff := (point_valid_above_imp_y_inf pabp' poep' eqx'').
rewrite subr_cp0 in ydiff.
rewrite subr_cp0 in y'diff.
have y''diff: (p_y p  < p_y p'').
  by rewrite (lt_le_trans  ydiff y'diff).
rewrite -eqx' in eqx''.
have := ax4_three_triangles p hl hr p''.
have /eqP pHleq :=  (pue_formula_vert hl eqx'').
have /eqP pHreq :=  (pue_formula_vert hr eqx'').

rewrite pue_formula_opposite in pHreq.
rewrite pue_formula_cycle in pHleq.

move : poepf'' pHleq => /eqP  ->  -> .
have :  pue_formula p p'' hr = - ((p_x p'' - p_x hr) * (p_y p - p_y p'')).
  by rewrite -pHreq opprK.
move => ->.
rewrite add0r addrC -mulrBl.
rewrite  [x in (x - _) * _ == _] addrC.
rewrite addrKA opprK.

rewrite /point_strictly_under_edge /= {pabhl pabhr vallow valhigh poep' poep'' poepf' puep pabp'}.
rewrite addrC.
rewrite -subr_gte0 in inH.
rewrite -subr_lt0 in y''diff.
move => /eqP <-.

by rewrite pmulr_rlt0.
Qed.

Lemma order_edges_viz_point c p :
valid_edge (low c) p -> valid_edge (high c) p ->
(low c) <| (high c) ->
p <<= (low c) -> p <<= (high c).
Proof.
move => vallow valhigh.
have  := (exists_point_valid  vallow  ) .
have := (exists_point_valid  valhigh  ) => [][] ph verhigh [] pl verlow.
have  := intersection_on_edge verlow => [][] poepl eqxl.
have  := intersection_on_edge verhigh => [][] poeph eqxh.
rewrite /right_form /edge_below => /orP [] /andP [].
  move => pueplow puephigh.
  apply (under_low_imp_under_high pueplow puephigh vallow valhigh).
move => pabpleft pabpright.
  apply (under_low_imp_under_high_bis pabpleft pabpright vallow valhigh).
Qed.  

Lemma order_edges_strict_viz_point c p :
valid_edge (low c) p -> valid_edge (high c) p ->
(low c) <| (high c) ->
p <<< (low c) ->  p <<< (high c).
Proof.
move => vallow valhigh.
have  := (exists_point_valid  vallow  ) .
have := (exists_point_valid  valhigh  ) => [][] ph verhigh [] pl verlow.
have  := intersection_on_edge verlow => [][] poepl eqxl.
have  := intersection_on_edge verhigh => [][] poeph eqxh.
rewrite /right_form /edge_below => /orP [] /andP [].
  set A := left_pt (low c).
  set B := right_pt (low c).
  move => pueplow puephigh.
  move =>  inf0.
  have := ltW inf0; rewrite -/A -/B => infeq0.
  by have := (under_low_imp_strict_under_high pueplow puephigh vallow valhigh inf0).
move=> pueplow puephigh.
move=> inf0.
by have := (under_low_imp_strict_under_high_bis pueplow puephigh vallow valhigh inf0).
Qed.

Definition dummy_pt := Bpt 0%:Q 0%:Q.
Definition dummy_event := Bevent dummy_pt [::].
Definition dummy_edge : edge := (@Bedge  dummy_pt (Bpt 1%:Q 0%:Q) isT).
Definition dummy_cell : cell := (@Bcell  (dummy_pt::[::]) (dummy_pt::[::]) dummy_edge dummy_edge).

(* if a cell doesn't contain a point, then either both edges are strictly under p or strictly over p *)
Definition contains_point (p : pt) (c : cell)  : bool :=
   ~~  (p <<< low c) && (p <<= (high c)).

Definition inside_open_cell p c :=
  contains_point p c && (p_x (head dummy_pt (left_pts c)) <= p_x p).

Definition inside_closed_cell p c :=
  contains_point p c && (p_x (head dummy_pt (left_pts c)) <= p_x p) && (p_x (head dummy_pt (right_pts c)) <= p_x p).

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
                        Bcell  (left_pts c) (no_dup_seq [:: p; p1]) (low c) (high c)::[::]
                    end
       | c::q =>  Bcell  (left_pts c) [::p] (low c) (high c)::closing_rest p q
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
                              Bcell  (left_pts only_cell) (no_dup_seq [:: p0; p; p1])(low only_cell) (high only_cell)::[::]
                      end
      | c::q => let op0 := vertical_intersection_point p (low c) in 
                    match op0 with 
                       | None => [::]
                       | Some(p0) =>
                        Bcell  (left_pts c) (no_dup_seq [:: p0; p]) (low c) (high c) :: (closing_rest p q)
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
                              (Bcell  (no_dup_seq ([:: p1; p; p0])) [::] low_e high_e) ::[::]
                      end
    | c::q => let op0 := vertical_intersection_point p low_e in 
                    match op0 with 
                       | None => [::]
                       | Some(p0) =>
                        (Bcell  (no_dup_seq([:: p; p0])) [::] low_e c) :: opening_cells p q c high_e
                    end
end.
(*
Fixpoint extract_h (cells : seq cell) (high_e : edge) : edge :=
  match cells with 
   [::] => high_e
   | c::q => extract_h q (high c)
  end.

Definition extract_l_h_edges (cells : seq cell) : edge * edge :=
  match cells with
    | [::] => (dummy_edge, dummy_edge)
    | c::q => (low c, extract_h q (high c))
end.

*)


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
(*
Fixpoint extract_last_cell (open_cells : seq cell) (contact_cells : seq cell) : seq cell  :=
  match open_cells with
    | [::] => [::]
    | c::q => if (contains contact_cells c) then [:: c] else extract_last_cell q contact_cells 
  end.
*)
Definition step (e : event) (open_cells : seq cell) (closed_cells : seq cell) : (seq cell) * (seq cell) :=
   let p := point e in
   let '(first_cells, contact_cells, last_cells, lower_edge, higher_edge) := open_cells_decomposition open_cells p in
  (* let (lower_edge, higher_edge) := extract_l_h_edges contact_cells in *)
   let closed := closing_cells p contact_cells in 
   let closed_cells := closed_cells++closed in
   let new_open_cells := opening_cells p (outgoing e) lower_edge higher_edge in
   (first_cells++new_open_cells++last_cells, closed_cells).

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
 
 Definition start (events : seq event) (bottom : edge) (top : edge) : seq cell :=
     match events with
       | [::] => [::]
       | e :: q => 
           let p := point e in let out := outgoing e in
            scan q (opening_cells p out bottom top) [::]
       end. 

Section proof_environment.
Variable bottom top : edge.


Definition lexPt (p1 p2 : pt) : bool :=
  (p_x p1 < p_x p2) || ((p_x p1 == p_x p2) && (p_y p1 < p_y p2)).

Definition lexPtEv (e1 e2 : event) : bool :=
  lexPt (point e1) (point e2).

Definition inside_box p :=
(~~ (p <<= bottom)  && (p <<< top) ) &&
  (valid_edge bottom p && valid_edge top p).


Definition event_close_edge ed ev : bool :=
right_pt ed == point ev.

Definition end_edge edge events : bool :=
(edge \in [:: top; bottom]) || has (event_close_edge edge) events.

Definition close_alive_edges open future_events : bool := 
all (fun c => (end_edge (low c) future_events) && (end_edge (high c) future_events)) open.

Definition close_out_from_event ev future : bool :=
  all (fun edge => end_edge edge future) (outgoing ev).

Fixpoint close_edges_from_events events : bool :=
  match events with
  | [::] => true
  | ev :: future_events => close_out_from_event ev future_events && close_edges_from_events future_events
  end.

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

Lemma lexPtEvtrans ev a future : sorted  lexPtEv (ev::a::future) ->
 sorted lexPtEv (ev :: future).
Proof.
rewrite /=.
case : future => [//|b future].
rewrite /=.
move => /andP [] evLea /andP [] aLeb pathbf.
rewrite pathbf andbT.
move : evLea aLeb.
rewrite /lexPtEv /lexPt.
(*case h : (p_x (point ev) < p_x (point a)) => /=.*)
have [h | h'] := boolP (p_x (point ev) < p_x (point a)) => /=.
move => _.
have [h2 | h2'] := boolP (p_x (point a) < p_x (point b)) => /=.
(* case h2 : (p_x (point a) < p_x (point b)) => /=.*)
move => _.
by rewrite (lt_trans h h2).
move /andP => [/eqP <-] _.
by rewrite h.
move => /andP []/eqP <-  evLa /orP [] evLb .
  by rewrite evLb.
apply /orP .
move : evLb => /andP [] /eqP <- aLb.

rewrite (lt_trans evLa aLb).
rewrite eq_refl  andbT  .
by right.
Qed.

Lemma lexPtevAbsicca a b : (lexPtEv a b) -> (p_x (point a)) <= (p_x (point b)).
Proof.
rewrite /lexPtEv.
move => /orP [] h.
by rewrite ltW.
by move : h => /andP [] /eqP <-.
Qed.


Lemma vertical_some_alive ed ev future :
p_x (left_pt ed) < p_x (point ev) -> sorted lexPtEv (ev::future) ->
end_edge ed (ev::future) -> inside_box (point ev) -> valid_edge ed (point ev).
Proof.
elim : future => [ lftedLev _ | b future Ih lftedLev].
  rewrite /end_edge.
  move => /orP [].
    rewrite !inE /inside_box =>  /orP [] /eqP ->  /andP [] /andP [] _ _  /andP [] _ //. 
  rewrite has_seq1 /event_close_edge => edincEv insbox.
  rewrite /valid_edge /andP ltW. 
    rewrite andTb.
    have h2 : right_pt ed = point ev.
      by apply /eqP.
    by rewrite h2.
  by [].
move => sorevBf.
have sorevF : sorted lexPtEv (ev :: future).
  by apply (lexPtEvtrans sorevBf ).
move => endevbfut ins.
have [/eqP h | h'] := boolP( right_pt ed == point b).
  rewrite /valid_edge.
  rewrite ltW => //.
  rewrite h.
  apply : lexPtevAbsicca .
  rewrite /= in sorevBf.
  by move /andP : sorevBf => [].
move : (endevbfut).
rewrite /end_edge .
move => /orP [].
  move: ins => ins1 ins2.
  apply : (Ih lftedLev sorevF _ ins1).
  by rewrite /end_edge /= ins2.
rewrite /= => /orP [] .
  rewrite /event_close_edge  /valid_edge => /eqP ->.
  rewrite ltW //.
  by rewrite le_eqVlt eqxx.
rewrite /event_close_edge.
rewrite (negbTE h') /=.
move => endfut.
apply : Ih => //.
rewrite /end_edge /=.
by rewrite endfut !orbT.
Qed.



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

Fixpoint adjacent_cells_aux open e : bool :=
  match open with
  | [::] => true
  | a::q => (e == low a) && adjacent_cells_aux q (high a)
  end.

Definition adjacent_cells open : bool :=
  match open with 
  | [::] => true
  | b::q => adjacent_cells_aux q (high b)
  end.
  
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
match vertical_intersection_point (Bpt maxleft 0%Q) e1 with
 | None => false
 | Some(p) => 
  match vertical_intersection_point (Bpt minright 0%Q) e1 with
    |None => false
    | Some(p2) =>
  (p <<= e2) && (p2 <<= e2)
  end
end.

Definition bottom_edge_seq_above (s : seq cell) (p : pt) :=
  if s is c :: _ then (p) <<= (low c) else true.

Definition bottom_edge_seq_below (s : seq cell) (p : pt) :=
  if s is c :: _ then ~~ (p <<< low c) else true.


Lemma under_onVstrict e p :
  valid_edge e p ->
  (p <<= e) = (p === e) || (p <<< e).
Proof.
move=> valep.
rewrite /point_under_edge /point_strictly_under_edge /point_on_edge.
by rewrite le_eqVlt valep andbT.
Qed.

Lemma onAbove e p : p === e -> ~~ (p <<< e).
Proof.
rewrite /point_on_edge /point_strictly_under_edge=> /andP[cmp valep].
by rewrite -leNgt le_eqVlt eq_sym cmp.
Qed.

Lemma strict_nonAunder e p :
  valid_edge e p ->
  (p <<< e) = (~~ (p === e)) && (p <<= e).
Proof.
move=> valep.
rewrite /point_strictly_under_edge /point_on_edge.
by rewrite valep andbT lt_neqAle.
Qed.

Lemma strict_under_cell (c : cell) (p : pt) :
  valid_cell c p ->
  right_form c -> p <<= (low c) -> ~~ contains_point p c ->
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

(* The relation edge_below (noted <| ) is transitive for edges that
  share their left point (as in outgoing edges. *)
Lemma trans_edge_below_out p e1 e2 e3 :
  left_pt e1 = p -> left_pt e2 = p -> left_pt e3 = p ->
  e1 <| e2 -> e2 <| e3 -> e1 <| e3.
Proof.
case: e1 => [d [a_x a_y] /= cpa].
case: e2 => [d' [b_x b_y] /= cpb].
case: e3 => [d'' [c_x c_y] /= cpc] dp d'p d''p.
rewrite /edge_below /point_under_edge /point_strictly_under_edge.
rewrite !pue_formulaE; simpl left_pt; simpl right_pt.
move: cpa cpb cpc; rewrite dp d'p d''p {dp d'p d''p}.
case: p=> [px py]; simpl p_x; simpl p_y=> cpa cpb cpc.
move=> c1' c2'.
have c1 : 0 <= pue_f px py a_x a_y b_x b_y.
  move: c1'; rewrite !(eqP (pue_f_eq _ _ _ _)) lexx ltxx !andTb -leNgt.
  by rewrite pue_f_o oppr_lte0 (pue_f_c px)=> /orP[].
have c2 : 0 <= pue_f px py b_x b_y c_x c_y.
  move: c2'; rewrite !(eqP (pue_f_eq _ _ _ _)) lexx ltxx !andTb -leNgt.
  by rewrite pue_f_o oppr_lte0 (pue_f_c px)=> /orP[].
move=> {c1' c2'}.
apply/orP; left.
rewrite (eqP (pue_f_eq _ _ _ _)) lexx andTb pue_f_o -pue_f_c oppr_lte0.
set p := {| p_x := px; p_y := py |}.
have aright : 0 < pue_formula p (subpoint p) {| p_x := a_x; p_y := a_y |}.
  by apply: point_sub_right.
have bright : 0 < pue_formula p (subpoint p) {| p_x := b_x; p_y := b_y |}.
  by apply: point_sub_right.
have cright : 0 < pue_formula p (subpoint p) {| p_x := c_x; p_y := c_y |}.
  by apply: point_sub_right.
rewrite pue_formulaE in aright; simpl p_x in aright; simpl p_y in aright.
rewrite pue_formulaE in bright; simpl p_x in bright; simpl p_y in bright.
rewrite pue_formulaE in cright; simpl p_x in cright; simpl p_y in cright.
rewrite -(pmulr_lge0 _ bright) -pue_f_ax5.
by apply: addr_ge0; rewrite pmulr_lge0.
Qed.

Lemma opening_cells_right_form e low_e high_e : 
sorted edge_below (outgoing e) ->
~~(point e <<< low_e) -> point e <<< high_e ->
low_e <| high_e ->
(forall g, g \in outgoing e -> left_pt g = (point e)) ->
(forall g, g \in outgoing e -> low_e <| g) ->
(forall g, g \in outgoing e -> g <| high_e) ->
forall new_open_cells, 
opening_cells (point e) (outgoing e) low_e high_e = new_open_cells ->
forall c, c \in new_open_cells -> 
  right_form c.
(*  && (head low_e [seq low c | c <- new_open_cells] == low_e). *)
Proof.
elim: (outgoing e) low_e => [ | g1 edges IH] low_e
  sorted_e pabove punder lowhigh outs alla allb /=.
  case v_i_l_eq : 
   (vertical_intersection_point (point e) low_e)=> [a1 | ];
   last by move=> s <- c.
  case v_i_h_eq :
   (vertical_intersection_point (point e) high_e) => [a2 | ];
   last by move=> s <- c.
  case: ifP => [a2e | a2ne];
    by case: ifP => [a1e | a1ne] s <- c; rewrite inE ?eqxx => /eqP ->;
    rewrite /right_form /= (* andbT *).
case v_i_l_eq : 
   (vertical_intersection_point (point e) low_e)=> [a1 | ];
   last by move=> s <- c.
have outs' : forall g, g \in edges -> left_pt g = point e.
  by move=> g gin; apply outs; rewrite inE gin orbT.
have alla' : forall g, g \in edges -> low_e <| g.
  by move=> g gin; apply alla; rewrite inE gin orbT.
have allb' : forall g, g \in edges -> g <| high_e.
  by move=> g gin; apply allb; rewrite inE gin orbT.
have sorte' : sorted edge_below edges by apply: (path_sorted sorted_e).
have g1belowhigh : g1 <| high_e by apply: allb; rewrite inE eqxx.
have px : (point e) = left_pt g1 by rewrite outs ?inE ?eqxx.
have validg1 : valid_edge g1 (point e).
  rewrite /valid_edge px lexx le_eqVlt orbC.
  by case: (g1)=> //= ? ? ->.
have paboveg1 : ~~ (point e <<< g1).
  by rewrite strict_nonAunder // negb_and negbK px left_on_edge.
have g1le : forall g, g \in edges -> g1 <| g.
  move: sorted_e outs.
  elim: edges g1
    {IH alla allb outs' alla' allb' sorte' g1belowhigh px
     validg1 paboveg1} => [ // | g2 edges IH].
  move=> g1 /= /andP[g1leg2 sorte] lefts g; rewrite inE=>/orP[/eqP -> //| gin].
  have lg1 : left_pt g1 = point e by apply: lefts; rewrite !inE eqxx.
  have lg2 : left_pt g2 = point e by apply: lefts; rewrite !inE eqxx orbT.
  have lg : left_pt g = point e by apply: lefts; rewrite !inE gin !orbT.
  apply: (trans_edge_below_out lg1 lg2 lg g1leg2).
  by apply: IH=> // g' g'in; apply: lefts; rewrite inE g'in orbT.
by case: ifP => [_ | _ ] s <- c; rewrite inE=> /orP[/eqP -> /= | ];
  (try solve[rewrite /right_form /=; apply: alla; rewrite inE eqxx; by []]);
  (apply: IH=> //); (try exact g1belowhigh); (try exact paboveg1).
Qed.

(*
Lemma order_cells_viz_point (cells : seq cell) p :
forall c, c \in cells ->
valid_edge (low c) p -> valid_edge (high c) p ->
right_form c ->
p <<= (low c) ->  p <<= (high c).
Proof.

*)

Definition s_right_form (s : seq cell)  : bool :=
  all (fun c => right_form c ) s.


Definition seq_valid (s : seq cell) (p : pt) : bool :=
    all (fun c => (valid_edge (low c) p) && (valid_edge (high c) p)) s.


Lemma insert_opening_valid first_cells new_open_cells last_cells p : 
seq_valid first_cells p -> seq_valid  new_open_cells p ->
seq_valid last_cells p -> seq_valid  (first_cells++new_open_cells++ last_cells) p.
Proof.
apply insert_opening_all.
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
right_form c ->
valid_edge (low c) (point e) /\ valid_edge (high c) (point e) ->
event_close_edge (low c) e \/  event_close_edge (high c) e->
contains_point (point e) c.
Proof.
rewrite /contains_point /event_close_edge .
move =>  rf val [/eqP rlc | /eqP rhc].
move : rf val.
  rewrite /point_strictly_under_edge -rlc {rlc}.
  have := (pue_formula_two_points (right_pt (low c)) (left_pt (low c))) => [][] _ [] /eqP -> _ /=.
  rewrite /right_form /edge_below.
  move => /orP [] /andP [] //= => pablhlow pabrhlow [] _ validrlhigh.
  apply :  not_strictly_above pablhlow pabrhlow validrlhigh.
  move : rf val.
rewrite /point_under_edge -rhc {rhc}.
have := (pue_formula_two_points (right_pt (high c)) (left_pt (high c))) => [] [] _ [] /eqP -> _ /=.
rewrite le0r /right_form /edge_below /= andbT=> /orP [] /andP [] //= => pablhlow pabrhlow [] valrhlow _ .
apply : not_strictly_under pablhlow pabrhlow valrhlow.
Qed.

Lemma contrapositive_close_imp_cont c e :
right_form c ->
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


Lemma contact_last_not_contain open_cells e high_e contact_cells :
bottom_edge_seq_above open_cells (point e) ->
s_right_form open_cells ->
seq_valid open_cells (point e) ->
adjacent_cells open_cells ->
forall contact last_c high_c, 
open_cells_decomposition_contact open_cells (point e) contact_cells high_e =
   (contact, last_c, high_c) ->
forall c, (c \in last_c) -> ~ contains_point (point e) c.
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
  have qval : (seq_valid q (point e)).
    move : opvalid.
    by rewrite /s_right_form /all => /andP [] _.
  have adjq : adjacent_cells q by apply: (adjacent_cons adj_op).
  have baq : bottom_edge_seq_above q (point e).
    move: contain; rewrite /contains_point /= => /andP[] _.
    rewrite /bottom_edge_seq_above; move: adj_op.
    by case: (q)=> //= a' q' => /andP[/eqP <- _]; rewrite ceq.
  by apply : (IH baq q_rf qval adjq last_c1 (rcons contact {| left_pts := lpts; right_pts := rpts;low := lowc; high := high_c |})  high_c h).
move =>  [] conteq lc heq {IH}.
rewrite -lc.
move => c1.
rewrite inE => /orP[ | c1inq].
  by move : notcontain => /negP notcontain /eqP  -> .
have rfc1 : (right_form c1).
  move : op_rf.
  rewrite /s_right_form .
  move =>  /allP /= incq /=.
  have := (incq c1).
  by rewrite inE c1inq orbT => // /(_ isT).
have valc1 : valid_edge (low c1) (point e) /\ valid_edge (high c1) (point e).
  move : opvalid.
  rewrite /seq_valid.
  move =>  /allP /= valcq /=.
  have := (valcq c1).
  rewrite inE c1inq orbT.
  move =>  a.
  apply /andP.
by apply a. 
have [vallc valhc] : valid_edge (low c) (point e) /\ valid_edge (high c) (point e).
  by move: opvalid => /allP /= /(_ c); rewrite inE eqxx => /(_ isT)=>/andP.
have lowhigh : (low c) <| (high c).
  by move: op_rf=> /allP /(_ c); rewrite inE eqxx /right_form => /(_ isT).
have underhigh : (point e) <<= (high_c).
  rewrite (_ : high_c = high c); last by rewrite ceq.
  by apply: order_edges_viz_point.
have strictunder : (point e) <<< (low c).
  by move: notcontain; rewrite ceq negb_and /= underhigh orbF negbK.
rewrite /right_form /edge_below in rfc1.
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
set e1 := @Bedge {|p_x := 0; p_y := 1|} {|p_x := 1; p_y := 1|} ltr01.
set e2 := @Bedge {|p_x := 0; p_y := 2%:R|} {|p_x := 1; p_y := 1|} ltr01.
set p := {|p_x := 3%:R; p_y := 0|}.
set c := Bcell [::] [::] e1 e2.
have := abs [::c] p isT isT isT isT c.
rewrite inE=> /(_ (eqxx _))=> [][] _.
compute; by [].
Qed.


Lemma fix_not_contain fc open_cells e   :
(forall c, c \in fc  -> ~ contains_point (point e) c) ->
s_right_form open_cells ->
seq_valid open_cells (point e) ->
adjacent_cells open_cells ->
bottom_edge_seq_below open_cells (point e) ->
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition_fix open_cells (point e) fc =
  (first_cells, contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) ->
~ contains_point (point e) c.
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
have valo : seq_valid (c2 :: q) (point e).
  rewrite -open_cells_eq.
  by apply/allP=> c' c'in; apply: (allP valc1); rewrite inE c'in orbT.
move: (adjc1); rewrite open_cells_eq => /andP[/eqP c1c2 adjc2'].
have adjo : adjacent_cells (c2 :: q) by exact adjc2'.
case: ifP => [contains | /negbT notcontains].
  case contact_eq : 
  (open_cells_decomposition_contact (c2 :: q) (point e) [::] hc1) =>
  [[contact_cells last_cells] edge1] [] <- _ <- _ _.
  move=> c /orP[cinfc | cinlc].
    by apply: cfc.
  have pundero : bottom_edge_seq_above (c2 :: q) (point e).
    by rewrite /= -c1c2 c1_eq; move: contains => /andP[] /=.
  by apply: (contact_last_not_contain _ _ _ _ contact_eq).
have belowc2 : bottom_edge_seq_below (c2 :: q) (point e).
  move: notcontains; rewrite -c1_eq negb_and negbK (negbTE pabovec1) /=.
  by rewrite /= c1c2 => /negP *; apply/negP/underWC.
move=> fixeq.  
have := IH (rcons fc c1); rewrite open_cells_eq c1_eq.
move=> /(_ _ rfo valo adjo belowc2 _ _ _ _ _ fixeq); apply.
move=> c; rewrite -cats1 mem_cat inE=> /orP[cinfc | /eqP ->].
  by apply: cfc.
by move : notcontains => /negP.
Qed.


Lemma decomposition_not_contain open_cells e : 
forall first_cells contact last_cells low_f high_f,
s_right_form open_cells ->
seq_valid open_cells (point e) ->
adjacent_cells open_cells ->
bottom_edge_seq_below open_cells (point e) ->
open_cells_decomposition open_cells (point e)  = (first_cells, contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) -> ~ contains_point (point e) c.
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
case : (outgoing e) => [/= |/= c q] newop.
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
  forall e,
  e \in (outgoing ev) -> left_pt e == point(ev).

Lemma valid_edge_extremities e0 p:
(left_pt e0 == p) || (right_pt e0 == p) ->
valid_edge e0 p.
Proof.
rewrite /valid_edge.
by move => /orP [/eqP eq |/eqP eq ];
rewrite -eq lexx ?andbT /= {eq} ltW // ; case : e0 .
Qed.

Lemma open_not_nil out low_e high_e p : 
valid_edge low_e p -> valid_edge high_e p ->
opening_cells p out low_e high_e != [::].
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

Lemma last_seq2 (T : Type) (def a : T) (s : seq T) :
   s <> nil -> last def (a :: s) = last def s.
Proof.
by case: s => [// | b s] _ /=.
Qed.

Lemma higher_edge_new_cells e low_e high_e:
out_left_event e ->
forall new_open_cells,
opening_cells (point e) (outgoing e) low_e high_e = new_open_cells ->
valid_edge low_e (point e) -> valid_edge high_e (point e) -> 
(high (last dummy_cell new_open_cells) == high_e).
Proof.
rewrite /out_left_event.
elim : (outgoing e) low_e  => [/= | ed q IH ] low_e outleft openc.
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
by apply /negP /underWC.
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
cells_low_e_top open low_e -> adjacent_cells_aux open low_e ->
~ p <<< low_e ->  p <<< top ->
(exists c : cell, c \in open /\ contains_point p c).
Proof.
elim : open low_e => [//= | c0 q IH ].

case cont : (contains_point p c0).
  exists c0.
  rewrite cont.
  apply : andP .
  by rewrite andbT inE eqxx .
have := (IH (high c0)).
move => IH' low_e {IH}.
rewrite /cells_low_e_top => /andP[] /andP [] _ /= /eqP <- hightop /andP [] _ adjaux.
move => lowunder topabove.
  have : cells_low_e_top q (high c0).
  rewrite /cells_low_e_top /=.
  have qnnil: q!= nil.
    move : hightop lowunder topabove  cont {IH'} adjaux.
    case : q => //.
    rewrite  /contains_point /=.
    move => /eqP ->  /negP -> pinftop.
    by rewrite  (underW pinftop). 
  rewrite qnnil /=.
  move : hightop qnnil adjaux IH'.
  case : q => [ // | a q /=].
  move => hightop.
  by rewrite hightop eq_sym => _ /andP [] ->.
move => lowtop /=.

rewrite /contains_point in cont.
move : lowunder cont  => /negP /= -> /= /negP phc0.
have phc := (underWC phc0  ).
have := (IH' lowtop adjaux phc topabove) .
move => [] x [] xinq cpx.
exists x .
by rewrite in_cons xinq /= orbT cpx.
Qed.

Lemma exists_cell  p open :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
(exists c : cell, c \in open /\ contains_point p c).
Proof.
case : open => [//= | c0 q].
rewrite /cells_bottom_top => cbt.
rewrite /adjacent_cells /= => adjqhc0.
have := (exists_cell_aux cbt _ _ _ ).
move : cbt.
rewrite /cells_low_e_top =>  /andP [] /andP [] _ /= /eqP -> _ .
rewrite eqxx adjqhc0 /= => exis /andP [] /andP [] /negP puepb puept _.
have puespb :=  (underWC puepb).
by apply : (exis p _ puespb puept).
Qed.


Lemma l_h_in_open (open : seq cell) p :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
exists lc hc, lc \in open /\ hc \in open /\ low lc = snd(fst (open_cells_decomposition open p)) /\ high hc = snd (open_cells_decomposition open p).
Proof.
elim : open => [//=| c open IH].
move => cbotomopn  adjopen  insbox .
have exc := (exists_cell cbotomopn adjopen  insbox).
case op_c_d : (open_cells_decomposition (c :: open) p) => [[[[fc cc] lc] low_e] high_e] /=.
have := (l_h_c_decomposition op_c_d exc) => [][] /eqP <- [] /eqP <- ccnil.
have := (decomposition_preserve_cells op_c_d) => ->.
have := (last_in_not_nil  dummy_cell ccnil) => lastincc.
have := (head_in_not_nil  dummy_cell ccnil) => headincc.
exists (head dummy_cell cc).
exists (last dummy_cell cc).
by rewrite !mem_cat headincc lastincc !orbT .
Qed.


Lemma opening_cells_close event low_e high_e future :
end_edge low_e future -> end_edge high_e future -> close_out_from_event event future ->
close_alive_edges (opening_cells (point event) (outgoing event) low_e high_e) future.
Proof.
rewrite /close_out_from_event.
move : low_e high_e.
elim : (outgoing event) => [ | e0 q Ho].
  move => low_e high_e end_low end_high.
  move => close_events.
  rewrite /opening_cells.
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

Definition adj_rel := [rel x y : cell | high x == low y].

Lemma adj_aux_path (x : cell) s :
    adjacent_cells_aux s (high x) = path adj_rel x s.
Proof.
by elim: s x => [// | y s Ih] x /=; rewrite Ih.
Qed.

Definition adjacent_cells' open : bool :=
    sorted adj_rel open.

Lemma adjacent_cell'_eq open : adjacent_cells' open = adjacent_cells open.
Proof.
by case: open => [// | c l]; rewrite /adjacent_cells' /= -adj_aux_path.
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

Lemma higher_lower_equality e  open :
out_left_event e ->
forall first_cells contact_cells last_cells low_e high_e,
open_cells_decomposition open (point e) =
(first_cells, contact_cells, last_cells, low_e, high_e) ->
forall new_cells,
(opening_cells (point e) (outgoing e) low_e high_e) = new_cells ->
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
move : low_e high_e.
rewrite /out_left_event.
elim out : (outgoing e) => [/= | c q IH] low_e high_e outl.
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
have cond : (forall e0: edge_eqType, e0 \in  q -> left_pt e0 == point e).
  move => e0 ein.
  apply : outl.
  by rewrite inE ein orbT.
apply (IH c high_e cond valc highv).
Qed. 


Lemma opening_left e low_e high_e:
out_left_event e ->
valid_edge low_e (point e) ->
valid_edge high_e (point e) ->
forall open_cells,
(opening_cells (point e) (outgoing e) low_e high_e) = open_cells ->
forall c , c\in open_cells ->
 ((left_pt (low c) == (point e)) || ((low c) == low_e) || ((low c) == high_e)) &&
 ((left_pt (high c) == (point e)) || ((high c) == low_e) || ((high c) == high_e)) . 
Proof.
move : low_e high_e.
rewrite /out_left_event.
elim out : (outgoing e) => [/= | c q IH] low_e high_e outl.
  rewrite /=.
  move => lowv highv.
  case : (vertical_intersection_point (point e) low_e) => [low_pt|]; first last.
    by move => _ <-.
  case : (vertical_intersection_point (point e) high_e) => [high_pt|]; first last.
    by move => _ <-.
   move => _ <- c.
   rewrite inE.
   move => /eqP -> /=.
   by rewrite !eqxx !orbT /=.
rewrite /=.
move => lowv highv.
case : (vertical_intersection_point (point e) low_e) => [low_pt|]; first last.
  by move => _ <-.
move => new new_eq.
rewrite -new_eq => c'.
rewrite inE .
move => /orP [|].
  move => /eqP -> /=.
  have : left_pt c == point e.
    apply outl.
    by rewrite inE eqxx .
  move => /eqP ->.
  by rewrite !eqxx !orbT /=.
move => cin.
have cond : (forall e0: edge_eqType, e0 \in  q -> left_pt e0 == point e).
  move => e0 ein.
  apply : outl.
  by rewrite inE ein orbT.
have valc : valid_edge c (point e).
  apply : valid_edge_extremities.
  have  : left_pt c == point e.
    apply : outl.
    by rewrite inE eqxx.
  move => /eqP ->.
  by rewrite eqxx.
have := (IH c high_e cond valc highv (opening_cells (point e) q c high_e) erefl c' cin) .
by move => /andP [] /orP [/orP[ ->|/eqP ->]| ->] /orP [/orP[ ->|/eqP ->]| ->]  ; rewrite /= ?orbT ?andbT//= outl // inE eqxx.
Qed.

Lemma valid_between_events g e p future : 
lexPt e p -> 
(forall e', e' \in future -> lexPt p (point e')) ->
valid_edge g e -> inside_box p -> end_edge g future ->
valid_edge g p.
Proof.
move => einfp pinffut vale.
rewrite /inside_box => /andP [] _ /andP [] botv topv.
rewrite /end_edge => /orP [].
  by rewrite !inE => /orP [/eqP -> | /eqP -> ].
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
have beseqb := bottom_imp_seq_below cbtop insboxe.
have dec_not_end := decomposition_not_end srf val_op_e adjop beseqb op_dec.
have open_eq := decomposition_preserve_cells op_dec.
have := (l_h_valid cbtop adjop  insboxe val_op_e op_dec) => [][] lowv highv.
rewrite open_eq in val_op_e.
have exi := exists_cell cbtop adjop insboxe.
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top open_eq => /andP [] /andP [] _ /eqP openbottom /eqP opentop.
have := (open_not_nil (outgoing e) lowv highv).
case op_new : (opening_cells (point e) (outgoing e) low_e high_e) => [//= | cnew q'' /=] _.
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
    by rewrite eqxx orbT.
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
    by rewrite -high_eq2 /end_edge !inE opentop eqxx .
  rewrite -high_eq2.
  move : adjop.
  rewrite open_eq (catA fc (c :: q) (c' :: q')) -(adjacent_cut c'); first last.
    rewrite -size_eq0 size_cat /= !addn_eq0 .
    have /eqP  := PeanoNat.Nat.neq_succ_0 (size q) => sizennil.
    by rewrite negb_and sizennil orbT.
  rewrite  last_cat /= => /andP []/andP [] /eqP -> _ _.
    have cin : c' \in c'::q'.
    by rewrite inE eqxx.
  by move: (allP close_lc (c') cin) => /andP [].
move : close_ev.
rewrite /= => /andP [] cle _.
have close_new:= opening_cells_close endlowe endhighe cle.
rewrite op_new in close_new.
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
(forall e', e' \in future_events -> lexPt p (point e')) ->
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

move => [] open2eq _.
rewrite -open2eq in close_all.
rewrite -open2eq{open2eq}.
have beseqb := bottom_imp_seq_below cbtop insboxe.
have dec_not_end := decomposition_not_end srf val_op_e adjop beseqb op_dec.
have open_eq := decomposition_preserve_cells op_dec.

have := (l_h_valid cbtop adjop  insboxe val_op_e op_dec) => [][] lowv highv.
rewrite open_eq in val_op_e.
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top open_eq => /andP [] /andP [] _ /eqP openbottom /eqP opentop.
have := (open_not_nil (outgoing e) lowv highv).
case op_new : (opening_cells (point e) (outgoing e) low_e high_e) => [//= | cnew q'' /=] _.
have := higher_lower_equality outlefte op_dec op_new exi lowv highv .
rewrite /= => [][] low_eq [] high_eq ccnnil.

case : cc op_dec open_eq val_op_e openbottom opentop low_eq high_eq ccnnil lhc => [//|c q  /=] op_dec open_eq val_op_e openbottom opentop low_eq high_eq ccnnil lhc.
have := opening_valid outlefte lowv highv.
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

Lemma adjacent_opening_aux  e low_e high_e:
out_left_event e ->
forall new_open_cells ,
opening_cells (point e) (outgoing e) low_e high_e = new_open_cells ->
valid_edge low_e (point e) -> valid_edge high_e (point e) -> 
adjacent_cells_aux new_open_cells low_e.
Proof.
rewrite /out_left_event.
elim : (outgoing e) low_e  => [/= | ed q IH ] low_e outleft openc.
  case h1 : (vertical_intersection_point (point e) low_e) => [pl |  /= ].
    case h2 : (vertical_intersection_point (point e) high_e) => [ph |  /= ].
      move => <-  _ /=  _.
      by rewrite eqxx.
      rewrite /=.
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
move => <-.
have : (valid_edge ed (point e)).
  apply valid_edge_extremities.
  by rewrite outleft // inE eqxx.
rewrite /= valid.
move : outleft.
move => /allP  /andP [/eqP lfteq /allP outleft].
move=> ved vlow vhigh.
rewrite /= eqxx /=.
by apply : IH.
Qed.

Lemma adjacent_opening  e low_e high_e:
out_left_event e ->
forall new_open_cells ,
opening_cells (point e) (outgoing e) low_e high_e = new_open_cells ->
valid_edge low_e (point e) -> valid_edge high_e (point e) -> 
adjacent_cells new_open_cells.
Proof.
move => outleft op.
case : op => [//=| c q /= opening vlow vhigh].
have := (adjacent_opening_aux outleft opening vlow vhigh).
by move => /= /andP [_] .
Qed.


Lemma adjacent_cut' l2 a lc :
l2 != nil -> 
((high (last dummy_cell l2) == low a) && 
adjacent_cells l2 &&
adjacent_cells (a::lc) ) =
adjacent_cells (l2 ++ a::lc).
Proof.
case : l2 => [//= | c2 q2 _].
rewrite /adjacent_cells.
rewrite /=.
rewrite ! adj_aux_path.
rewrite -cat_rcons.
rewrite cat_path.
rewrite last_rcons.
rewrite rcons_path.
congr (_ && _).
rewrite andbC.
by [].
Qed.


Lemma adjacent_cut_rcons' l2 a fc :
l2 != nil -> 
( high a == (low (head dummy_cell l2))) && 
adjacent_cells l2 &&
adjacent_cells (rcons fc a)  =
adjacent_cells ((rcons fc a) ++ l2).
Proof.
rewrite cat_rcons.
move => lnnil.
case : fc => [/= | c q ].
rewrite andbT.
rewrite /adjacent_cells.
by case : l2 lnnil => [//| c2 q2 _ /=].

rewrite -!adjacent_cell'_eq /adjacent_cells'.
rewrite -cats1 /=.
rewrite !cat_path /=.
rewrite andbT !andbA.
rewrite (andbAC _ (_ == _)) .
congr (_ && _).
rewrite [ in RHS ] andbC.
congr (_ && _).
by case : l2 lnnil => [//| c2 q2 _ /=].
Qed.

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

Lemma replacing_seq_adjacent l1 l2 fc lc : 
l1 != nil -> l2 != nil -> 
low (head dummy_cell l1) = low (head dummy_cell l2) ->
high (last dummy_cell l1) = high (last dummy_cell l2) ->
adjacent_cells (fc ++ l1 ++ lc) ->
adjacent_cells l2 ->
adjacent_cells (fc ++ l2 ++ lc).
Proof.
case : fc => [//= | c q].

  case : l1 => [//= | c1 q1 _ ] .
  case : l2  => [//=| c2 q2  _ /= ].
  rewrite !adj_aux_path.
  rewrite !cat_path.
  move => /= Hlow Hhigh.
  move => /andP [] /= pathq1 pathlc ->  /= .
  case : lc pathlc => [//= | cl ql /= ].
  by rewrite Hhigh.

rewrite /adjacent_cells /=.
move => H1 H2 H3 H4 H5.
have := (replacing_seq_adjacent_aux   H1 H2 H3 H4 H5).
case : l2 H2 H3 H4=> [//=| c2 q2 _ /= ].
move => <- Hhigh H .
move : H5.
rewrite adj_aux_path.
rewrite !cat_path.
move => /andP [] _ /andP [].
case : l1 H1 Hhigh H => [//= | c1 q1 _ /= ].
move => Hhigh H /andP [] /eqP H2 H3.
by rewrite H2 eqxx in H .
Qed. 




Lemma step_keeps_adjacent open  e (future_events : seq event)  :
inside_box (point e) -> 
out_left_event e ->
seq_valid open (point e) ->
cells_bottom_top open ->
forall closed open2 closed2, 
 step e open closed = (open2, closed2) ->
adjacent_cells open -> adjacent_cells open2.
Proof.
rewrite /step .
move => insbox  outleft  validopen cbtop closed open2 closed2.
case op_c_d : (open_cells_decomposition open (point e)) =>  [[[[first_cells contact_cells] last_cells ]low_e] high_e].
move => [] <- _ adjopen.
have exi := (exists_cell cbtop adjopen insbox ).
have openeq := decomposition_preserve_cells op_c_d.
have := (l_h_valid cbtop adjopen  insbox validopen op_c_d).
move => [] lowv highv.
have := (open_not_nil (outgoing e) lowv highv).
case op_new : (opening_cells (point e) (outgoing e) low_e high_e) => [//= | q l ] qlnnil.
have := higher_lower_equality outleft op_c_d op_new exi lowv highv => [][] l_eq [] h_eq c_nnil.
have := (adjacent_opening outleft op_new lowv highv) => adjnew.
rewrite openeq in adjopen.
apply : (replacing_seq_adjacent c_nnil qlnnil l_eq h_eq adjopen adjnew).
Qed.


Lemma l_h_valid2 (open : seq cell) (p : pt) :
 inside_box p  -> 
open != nil -> 
let '(fc,c_c,last_c,lower,higher) := (open_cells_decomposition open p) in 
valid_edge lower p /\ valid_edge higher p.
Proof.
Admitted.

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
move => [] <- _.
have := (l_h_valid cbtop adjopen insbox openvalid op_c_d).
move => [] lowv highv.
have exi := (exists_cell cbtop adjopen insbox ).
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top => /andP [] /andP [] opnnil /eqP openbottom /eqP _.
have newnnil := open_not_nil (outgoing e) lowv highv.
have newopnnil := (middle_seq_not_nil first_cells last_cells newnnil).
rewrite newopnnil /=.
case op_new : (opening_cells (point e) (outgoing e) low_e high_e) => [// | c q].
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
have op_dec := (decomposition_preserve_cells op_c_d).
move => [] <- _.
have := (l_h_valid cbtop adjopen insbox openvalid op_c_d).
move => [] lowv highv.
have exi := (exists_cell cbtop adjopen insbox ).
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top => /andP [] /andP [] opnnil /eqP _ /eqP opentop.
have newnnil := open_not_nil (outgoing e) lowv highv.
have newopnnil := (middle_seq_not_nil first_cells last_cells newnnil).
case op_new : (opening_cells (point e) (outgoing e) low_e high_e) => [// | c q].
  by rewrite op_new in newnnil.
have := higher_lower_equality outleft op_c_d op_new exi lowv highv => [][] _ [] /= h_eq c_nnil.
case : last_cells op_c_d op_dec newopnnil => [/= op_c_d |c1 q1 _ op_dec /=]  .
  rewrite !cats0 -opentop last_cat  => -> newn_nil /=.
  rewrite last_cat -h_eq.
  by case  : contact_cells c_nnil h_eq op_c_d.
by rewrite -opentop op_dec !last_cat /= last_cat.
Qed.


Lemma every_point_inside_cell e (future_events : seq event) p old_open : 
inside_box p -> 
inside_box (point e) ->
out_left_event e ->
s_right_form old_open ->
seq_valid old_open (point e) ->
adjacent_cells old_open ->
cells_bottom_top old_open ->
close_alive_edges old_open (e :: future_events) ->
close_edges_from_events (e :: future_events) ->
(forall c, c \in old_open -> lexPt (last dummy_pt (left_pts c)) (point e)) ->
forall new_open new_closed closed, 
step e old_open closed  = (new_open, new_closed) ->
(lexPt (point e) p) -> (forall e2, e2 \in future_events -> lexPt p (point e2)) ->
forall c, c \in new_open -> lexPt (last dummy_pt (left_pts c)) p.
Proof.
move => insboxp insboxe outlefte srf openval adjopen cbtom close_ed close_ev new_open new_closed closed step einfp pinfe'. 
have cbtop_new := step_keeps_bottom_top insboxe openval adjopen cbtom outlefte step.
have adj_new := step_keeps_adjacent future_events insboxe outlefte openval cbtom step adjopen.
have val_new := step_keeps_valid insboxp insboxe einfp outlefte srf cbtom adjopen openval close_ed close_ev pinfe' step.
have := exists_cell cbtop_new adj_new insboxp => [][]c [] cin cont.
exists c.

rewrite /inside_open_cell cin cont /=; split .
  by [].
Admitted.


Lemma size_open_ok (p : pt) (out : seq edge) (low_e : edge) (high_e : edge) :   
let open :=  opening_cells p out low_e high_e in  
(size open = size out + 1)%N. 
 Proof.

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




(*
Definition events_inside_bottom_top events bottom top : Prop := 
  (p_x (left_pt bottom) = p_x (left_pt top)) && (p_x (left_pt bottom) = p_x (left_pt top))
*)

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

