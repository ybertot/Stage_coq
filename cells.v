
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

Lemma pue_f_triangle_on_edge a_x a_y b_x b_y p_x p_y p'_x p'_y :
pue_f a_x a_y b_x b_y p'_x p'_y == 0 ->
(b_x - a_x) * pue_f a_x a_y p_x p_y p'_x p'_y ==
(p'_x - a_x) * pue_f a_x a_y p_x p_y b_x b_y .
Proof.
move=> on_ed.
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_triangle_on_edge' a_x a_y b_x b_y p_x p_y p'_x p'_y :
pue_f a_x a_y b_x b_y p'_x p'_y == 0 ->
(b_x - a_x) * pue_f p_x p_y b_x b_y p'_x p'_y ==
(b_x - p'_x) * pue_f a_x a_y p_x p_y b_x b_y .
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

Lemma pue_f_triangle_decompose a_x a_y b_x b_y c_x c_y d_x d_y :
  pue_f a_x a_y c_x c_y d_x d_y = 0 ->
  pue_f a_x a_y b_x b_y c_x c_y =
  pue_f a_x a_y b_x b_y d_x d_y +
  pue_f b_x b_y c_x c_y d_x d_y.
Proof.
move=> online.
rewrite -(eqP (ax4 _ _ _ _ _ _ d_x d_y)).
rewrite addrC; congr (_ + _).
by rewrite addrC pue_f_o pue_f_c online oppr0 add0r -pue_f_c.
Qed.

Definition mkmx2 (a b c d : R) :=
  \matrix_(i < 2, j < 2)
    if (i == ord0) && (j == ord0) then a
    else if i == ord0 then b
           else if j == ord0 then c else d.

Definition mkcv2 (a b : R) := \col_(i < 2) if i == ord0 then a else b.

Lemma det_mkmx2 a_x a_y b_x b_y :
  \det(mkmx2 a_x a_y b_x b_y) = a_x * b_y - a_y * b_x.
Proof.
rewrite /mkmx2 (expand_det_row _ ord0) big_ord_recr /= big_ord1 /=.
by rewrite /cofactor /= expr0 expr1 mulNr !mul1r !det_mx11 !mxE /= mulrN.
Qed.

Lemma line_intersection a_x a_y b_x b_y c_x c_y d_x d_y :
  c_x < d_x ->
  0 < pue_f a_x a_y b_x b_y c_x c_y ->
  pue_f a_x a_y b_x b_y d_x d_y < 0 ->
  exists p_x p_y,
    pue_f a_x a_y b_x b_y p_x p_y = 0 /\
    pue_f c_x c_y d_x d_y p_x p_y = 0 /\
    (forall q_x q_y, pue_f a_x a_y b_x b_y q_x q_y = 0 ->
       pue_f c_x c_y d_x d_y q_x q_y = 0 -> p_x = q_x /\ p_y = q_y).
Proof.
move=> cltd cabove cunder.
set A := a_y - b_y; set B := b_x - a_x; set C := \det(mkmx2 a_x a_y b_x b_y).
have puef1_id x y : pue_f a_x a_y b_x b_y x y = A * x + B * y + C.
  by rewrite /A /B /C det_mkmx2 /pue_f; mc_ring.
set D := c_y - d_y; set E := d_x - c_x; set F := \det(mkmx2 c_x c_y d_x d_y).
have puef2_id x y : pue_f c_x c_y d_x d_y x y = D * x + E * y + F.
  by rewrite /D /E /F det_mkmx2 /pue_f; mc_ring.
set M := mkmx2 A B D E.
set V1 := mkcv2 (b_x - a_x) (b_y - a_y).
set V2 := mkcv2 (d_x - c_x) (d_y - c_y).
have sys_to_mx_eqn :
  forall x y, (A * x + B * y + C = 0 /\ D * x + E * y + F = 0) <->
   (M *m mkcv2 x y + mkcv2 C F = 0).
  move=> x y; split.
    move=> [eq1 eq2]; apply/matrixP=> i j.
    rewrite !mxE big_ord_recr /= big_ord1 /= !mxE.
    by case : j => [ [ | j ] ] //= _; case : i => [ [ | [ | i]]].
  move/matrixP=> mxq.
  split.
    have := mxq (Ordinal (isT : (0 < 2)%N)) (Ordinal (isT : (0 < 1)%N)).
    by rewrite !mxE big_ord_recr /= big_ord1 /= !mxE.
  have := mxq (Ordinal (isT : (1 < 2)%N)) (Ordinal (isT : (0 < 1)%N)).
  by rewrite !mxE big_ord_recr /= big_ord1 /= !mxE.
set sol := - (M ^-1 *m mkcv2 C F).
have soleq : sol = mkcv2 (sol ord0 ord0) (sol ord_max ord0).
  apply/matrixP=> [][[ | [ | i]]] // ip [ [ | j]] // jp; rewrite /= !mxE /=;
    (rewrite (_ : Ordinal jp = ord0); last apply: val_inj=> //).
    by rewrite (_ : Ordinal ip = ord0); last apply: val_inj.
  by rewrite (_ : Ordinal ip = ord_max); last apply: val_inj.
have detm : \det M != 0.
  have dets : \det M = A * E - D * B.
    rewrite (expand_det_col _ ord0) big_ord_recr /= big_ord1 !mxE /= /cofactor.
    by rewrite !det_mx11 /= expr1 expr0 !mulNr !mulrN !mul1r !mxE.
  have -> : \det M = pue_f a_x a_y b_x b_y d_x d_y -
                  pue_f a_x a_y b_x b_y c_x c_y.
    by rewrite dets /pue_f /A /B /D /E; mc_ring.
  rewrite subr_eq0; apply/eqP=> abs; move: cabove cunder; rewrite abs=> ca cu.
  by have := lt_trans ca cu; rewrite ltxx.
have Munit : M \in unitmx by rewrite unitmxE unitfE.
have solm : M *m sol + mkcv2 C F = 0.
  rewrite /sol mulmxN mulmxA mulmxV; last by rewrite unitmxE unitfE.
  by rewrite mul1mx addNr.
move: (solm); rewrite soleq -sys_to_mx_eqn => [][sol1 sol2].
exists (sol ord0 ord0), (sol ord_max ord0).
split; first by rewrite puef1_id.
split; first by rewrite puef2_id.
move=> qx qy; rewrite puef1_id puef2_id=> tmp1 tmp2; have := conj tmp1 tmp2.
rewrite sys_to_mx_eqn addrC => /addr0_eq solmq {tmp1 tmp2}.
suff : mkcv2 qx qy = sol.
  move/matrixP=> mxq; split.
    by rewrite -(mxq ord0 ord0) mxE.
  by rewrite -(mxq ord_max ord0) mxE.
rewrite -(mul1mx (mkcv2 qx qy)) -[in LHS](mulVmx Munit) -!mulmxA.
by rewrite -solmq mulmxN.
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
pue_formula a b p' == 0 ->
(p_x b - p_x a) * pue_formula a p p' ==
(p_x p' - p_x a) * pue_formula a p b.
Proof.
move : a b p p' => [ax ay] [b_x b_y] [px py] [p'x p'y] /=.
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

Lemma edge_and_left_vertical (p q a : pt) :
  p_x p < p_x a -> p_x p = p_x q ->
  (0 < pue_formula p q a) = (p_y q < p_y p).
Proof.
case: p=> [px py]; case: a=> [ax ay]; case: q=> [qx qy] /=.
move=> edge_cond <-.
rewrite (addrAC (ax * py)) addrNK opprD addrA opprK.
rewrite -mulrBl -addrA -mulrBl.
rewrite -(opprB ax px) mulNr -mulrBr.
by rewrite pmulr_rgt0 subr_gt0.
Qed.

Lemma edge_and_left_vertical_eq (p q a : pt) :
  p_x p < p_x a -> p_x p = p_x q ->
  (pue_formula p q a == 0) = (p == q).
Proof.
move=> edge_cond vert_cond.
apply/idP/idP; last first.
  by move/eqP ->; rewrite (pue_formula_two_points q a).1.
move=> abs; suff : p_y p = p_y q.
  by move: vert_cond {edge_cond abs}; case: p=> [? ?]; case q=> [? ?]/= <- <-.
apply: le_anti; rewrite leNgt.
rewrite -(edge_and_left_vertical edge_cond vert_cond) (eqP abs).
have ec' : p_x q < p_x a by rewrite -vert_cond.
rewrite leNgt -(edge_and_left_vertical ec' (esym vert_cond)).
by rewrite pue_formula_opposite -pue_formula_cycle (eqP abs) oppr0 ltxx.
Qed.

Lemma edge_and_right_vertical (p q a : pt) :
  p_x a < p_x p -> p_x p = p_x q ->
  (0 < pue_formula p q a) = (p_y p < p_y q).
Proof.
case: p=> [px py]; case: a=> [ax ay]; case: q=> [qx qy] /=.
move=> edge_cond <-.
rewrite (addrAC (ax * py)) addrNK opprD addrA opprK.
rewrite -mulrBl -addrA -mulrBl.
rewrite -(opprB px ax) mulNr addrC -mulrBr.
by rewrite pmulr_rgt0 subr_gt0.
Qed.

Lemma point_sub_right (p a : pt) :
  (p_x p < p_x a) -> 0 < pue_formula p (subpoint p) a.
Proof.
move=> edge_cond.
by rewrite edge_and_left_vertical //; rewrite /subpoint /= lter_sub_addr cpr_add.
Qed.

Lemma underW p e :
  (p <<< e) ->
  (p <<= e).
Proof.
rewrite /point_under_edge /point_strictly_under_edge.
apply : ltW .
Qed.

Lemma underWC p e :
~~ (p <<= e) -> ~~ (p <<< e).
Proof. by move/negP=> it; apply/negP=> it'; case: it; apply : underW. Qed.

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

Definition below_alt (e1 : edge) (e2 : edge) :=
  edge_below e1 e2 \/ edge_below e2 e1.

Lemma below_altC e1 e2 : below_alt e1 e2 <-> below_alt e2 e1.
Proof. by rewrite /below_alt or_comm. Qed.

Definition inter_at_ext (e1 e2 : edge) :=
  e1 = e2 \/
  forall p, p === e1 -> p === e2 -> p \in [:: left_pt e1; right_pt e1].

Definition inter_at_ext' (e1 e2 : edge) :=
  e1 = e2 \/
  forall p, p === e2 -> p === e1 -> p \in [:: left_pt e2; right_pt e2].

Lemma inter_at_ext_sym (s : seq edge) :
  {in s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s &, forall e1 e2, inter_at_ext' e1 e2}.
Proof.
move=> cnd e1 e2 e1in e2in; case: (cnd e2 e1 e2in e1in).
  by move=> ->; left.
by move=> subcnd; right=> p pe2 pe1; apply: subcnd.
Qed.

Definition no_crossing := forall e1 e2, below_alt e1 e2.

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
have := (pue_formula_triangle_on_edge p (p_on_edge_p')).

have /eqP := (pue_formula_vert l eqx  ) => ->.
have inle: (p_x r - p_x l) >0.
  by rewrite subr_cp0.
move => /eqP a.
have pminusl : (0 <= p_x p - p_x l).
  by rewrite subr_cp0.
  rewrite pue_formula_opposite -pue_formula_cycle oppr_le0 => lprpos.
have := (mulr_ge0 pminusl lprpos).
rewrite eqx -a.
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
have := (pue_formula_triangle_on_edge p (p_on_edge_p')).
have /eqP := (pue_formula_vert l eqx  )=> -> /eqP a.
rewrite pue_formula_opposite -pue_formula_cycle oppr_lt0=> lprpos.
have := mulr_gt0 pminusl lprpos.
rewrite eqx -a.
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
have := (pue_formula_triangle_on_edge p (p_on_edge_p')).

have /eqP := (pue_formula_vert l eqx  ) => ->.
have inle: (p_x r - p_x l) >0.
  by rewrite subr_cp0.
move => /eqP a.
have pminusl : (0 <= p_x p - p_x l).
  by rewrite subr_cp0.
  rewrite pue_formula_opposite -pue_formula_cycle oppr_lt0 -leNgt => lprpos.
have := mulr_ge0_le0 pminusl lprpos.
rewrite eqx -a pmulr_rle0 //.

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

Lemma order_edges_viz_point' low_e high_e p :
valid_edge low_e p -> valid_edge high_e p ->
low_e <| high_e ->
p <<= low_e -> p <<= high_e.
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

Lemma order_edges_viz_point c p :
valid_edge (low c) p -> valid_edge (high c) p ->
(low c) <| (high c) ->
p <<= (low c) -> p <<= (high c).
Proof. apply : order_edges_viz_point'. Qed.

Lemma order_edges_strict_viz_point' low_e high_e p :
valid_edge low_e p -> valid_edge high_e p ->
low_e <| high_e ->
p <<< low_e ->  p <<< high_e.
Proof.
move => vallow valhigh.
have  := (exists_point_valid  vallow  ) .
have := (exists_point_valid  valhigh  ) => [][] ph verhigh [] pl verlow.
have  := intersection_on_edge verlow => [][] poepl eqxl.
have  := intersection_on_edge verhigh => [][] poeph eqxh.
rewrite /right_form /edge_below => /orP [] /andP [].
  set A := left_pt low_e.
  set B := right_pt low_e.
  move => pueplow puephigh.
  move =>  inf0.
  have := ltW inf0; rewrite -/A -/B => infeq0.
  by have := (under_low_imp_strict_under_high pueplow puephigh vallow valhigh inf0).
move=> pueplow puephigh.
move=> inf0.
by have := (under_low_imp_strict_under_high_bis pueplow puephigh vallow valhigh inf0).
Qed.

Lemma order_edges_strict_viz_point c p :
valid_edge (low c) p -> valid_edge (high c) p ->
(low c) <| (high c) ->
p <<< (low c) ->  p <<< (high c).
Proof. apply: order_edges_strict_viz_point'. Qed.

Definition dummy_pt := Bpt 0%:Q 0%:Q.
Definition dummy_event := Bevent dummy_pt [::].
Definition dummy_edge : edge := (@Bedge  dummy_pt (Bpt 1%:Q 0%:Q) isT).
Definition dummy_cell : cell := (@Bcell  (dummy_pt::[::]) (dummy_pt::[::]) dummy_edge dummy_edge).

(* if a cell doesn't contain a point, then either both edges are strictly under p or strictly over p *)
Definition contains_point (p : pt) (c : cell)  : bool :=
   ~~  (p <<< low c) && (p <<= (high c)).

Definition right_limit c :=
  min (p_x (right_pt (low c))) (p_x (right_pt (high c))).

Definition inside_open_cell p c :=
  [&& contains_point p c,
      p_x (last dummy_pt (left_pts c)) <= p_x p &
      p_x p <= right_limit c].

Definition inside_closed_cell p c :=
  contains_point p c && (p_x (last dummy_pt (left_pts c)) <= p_x p) && ( p_x p <= p_x (last dummy_pt (right_pts c))).

Lemma intersection_middle_au e1 e2 :
  ~~ (left_pt e2 <<= e1) -> right_pt e2 <<< e1 ->
  exists p, pue_formula p (left_pt e1) (right_pt e1) = 0 /\ p === e2.
Proof.
rewrite /point_under_edge -pue_formula_cycle pue_formulaE -ltNge => ca.
rewrite /point_strictly_under_edge -pue_formula_cycle pue_formulaE => cu.
have [px [py []]] := line_intersection (edge_cond e2) ca cu.
rewrite -/(p_y (Bpt px py)); set py' := (p_y (Bpt px py)).
rewrite -/(p_x (Bpt px py)) /py'.
rewrite -pue_formulaE pue_formula_cycle=> on_line1.
case; rewrite -pue_formulaE pue_formula_cycle=> on_line2.
have := @line_intersection _ (p_x (left_pt e1)) (p_y (left_pt e1))
  (p_x (right_pt e1)) (p_y (right_pt e1))
 (p_x (left_pt e2)) (p_y (left_pt e2))
  (p_x (right_pt e2)) (p_y (right_pt e2))
  (edge_cond e2) ca.
move=> _; move: ca cu; rewrite -!pue_formulaE => ca cu.
exists (Bpt px py); split; first by rewrite on_line1.
rewrite /point_on_edge on_line2 eqxx /valid_edge /=.
have/eqP ol2 := on_line2.
have := pue_formula_on_edge (left_pt e1) (right_pt e1) ol2 => /=.
rewrite (pue_formula_cycle _ (Bpt _ _)) on_line1 mulr0 addr0 => /eqP signcond.
case : (ltrgtP px (p_x (right_pt e2))).
- rewrite andbT -subr_gt0 -subr_le0 => pe2.
  move: ca; rewrite -(pmulr_rgt0 _ pe2) -signcond.
  by rewrite nmulr_lgt0 // => /ltW.
- rewrite andbF -subr_lt0=> pe2.
  move: ca; rewrite -(nmulr_rlt0 _ pe2) -signcond.
  rewrite nmulr_llt0 // subr_gt0.
  move: pe2; rewrite subr_lt0=> rp pl; have := (lt_trans rp pl).
  by case: ltrgtP (edge_cond e2).
move=> pr; move: signcond; rewrite pr subrr mul0r=> /eqP; rewrite mulf_eq0.
move=> /orP[].
  by rewrite subr_eq0 => /eqP abs; have:= edge_cond e2; rewrite abs ltxx.
by move=>/eqP abs; move: cu; rewrite abs ltxx.
Qed.

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
   let new_open_cells :=
     opening_cells p (sort edge_below (outgoing e)) lower_edge higher_edge in
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

Definition start (events : seq event) (bottom : edge) (top : edge) :
  seq cell * seq cell :=
  scan events [:: Bcell (leftmost_points bottom top) [::] bottom top] [::].

Section proof_environment.
Variable bottom top : edge.


Definition lexPt (p1 p2 : pt) : bool :=
  (p_x p1 < p_x p2) || ((p_x p1 == p_x p2) && (p_y p1 < p_y p2)).

Definition lexePt (p1 p2 : pt) : bool :=
    (p_x p1 < p_x p2) || ((p_x p1 == p_x p2) && (p_y p1 <= p_y p2)).

Definition lexPtEv (e1 e2 : event) : bool :=
  lexPt (point e1) (point e2).

Lemma lexPtW p1 p2 :
  lexPt p1 p2 -> lexePt p1 p2.
Proof.
rewrite /lexPt /lexePt =>/orP [-> //=| /andP [] -> y_ineq].
rewrite ltW //. 
by rewrite orbT.
Qed.

Lemma lexePtNgt (p1 p2 : pt) : lexePt p1 p2 = ~~lexPt p2 p1.
Proof.
rewrite /lexePt /lexPt negb_or negb_and.
rewrite andb_orr -leNgt (andbC (_ <= _)) (eq_sym (p_x p2)) -lt_neqAle.
rewrite -leNgt (le_eqVlt (p_x p1)).
by case: (p_x p1 < p_x p2) => //; rewrite ?orbF //=.
Qed.

Lemma lexPtNge (p1 p2 : pt) : lexPt p1 p2 = ~~lexePt p2 p1.
Proof.
rewrite /lexePt /lexPt.
rewrite negb_or -leNgt negb_and (eq_sym (p_x p2)) andb_orr (andbC (_ <= _)).
rewrite -lt_neqAle le_eqVlt -ltNge.
by case: (p_x p1 < p_x p2); rewrite // ?orbF.
Qed.

Lemma lexePt_eqVlt (p1 p2 :pt) : lexePt p1 p2 = (p1 == p2) || lexPt p1 p2.
Proof.
rewrite /lexePt /lexPt.
case: (ltrgtP (p_x p1) (p_x p2))=> cnd; rewrite ?orbT //= ?orbF.
  by apply/esym/negP=> /eqP p1p2; move: cnd; rewrite p1p2 ltxx.
apply/idP/idP.
  rewrite orbC le_eqVlt=> /orP[/eqP | ->// ].
  move: cnd; case: p1 => [a b]; case: p2 => [c d]/= -> ->.
  by rewrite eqxx orbT.
by move/orP=> [/eqP -> // | /ltW].
Qed.

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

Lemma close_edges_from_events_step events :
  close_edges_from_events events = match events with
  | [::] => true
  | ev :: future_events => close_out_from_event ev future_events && close_edges_from_events future_events
  end.
Proof. by case: events. Qed.

Lemma lexePt_refl :
reflexive lexePt.
Proof.
rewrite /reflexive /lexePt=> p.
by rewrite eqxx le_refl /= orbT.
Qed.

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

Lemma lexPt_trans  : transitive lexPt.
Proof.
  rewrite /transitive /lexPt => p2 p1 p3 => /orP [xineq /orP [xineq2| /andP []/eqP <- yineq]|/andP []/eqP -> yineq /orP [-> //|/andP [] /eqP -> yineq2]] .
      by rewrite (lt_trans xineq xineq2).
    by rewrite xineq.
  by rewrite (lt_trans yineq yineq2) eqxx orbT.
Qed.

Lemma lexePt_lexPt_trans p1 p2 p3 : 
lexePt p1 p2 -> lexPt p2 p3 -> lexPt p1 p3.
Proof.
rewrite /lexePt /lexPt => /orP  [x_ineq|/andP  [] /eqP -> y_ineq /orP [-> // |/andP []/eqP -> y_s]].
  have : lexPt p1 p2.
    by rewrite /lexPt x_ineq.
  by apply lexPt_trans.
by rewrite( le_lt_trans y_ineq y_s) eqxx /= orbT.
Qed.

Lemma lexPt_lexePt_trans p1 p2 p3 :
lexPt p1 p2 -> lexePt p2 p3 -> lexPt p1 p3.
Proof.
move/[swap].
rewrite /lexePt /lexPt => /orP  [x_ineq|/andP  [] /eqP -> y_ineq /orP [-> // |/andP []/eqP -> y_s]].
  have : lexPt p2 p3.
    by rewrite /lexPt x_ineq.
  move/[swap]; apply lexPt_trans.
by rewrite( lt_le_trans y_s y_ineq) eqxx /= orbT.
Qed.

Lemma lexePt_trans : transitive lexePt.
move => p2 p1 p3; rewrite lexePt_eqVlt => /orP[/eqP-> // | p1p2] p2p3.
by apply/lexPtW/(lexPt_lexePt_trans p1p2).
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

Definition s_right_form (s : seq cell)  : bool :=
  all (fun c => right_form c ) s.

Lemma opening_cells_right_form e low_e high_e :
~~(point e <<< low_e) -> point e <<< high_e ->
low_e <| high_e ->
{in outgoing e, forall g, left_pt g = point e} ->
{in outgoing e, forall g, low_e <| g} ->
{in outgoing e, forall g, g <| high_e} ->
{in outgoing e &, no_crossing} ->
forall new_open_cells,
opening_cells (point e) 
  (sort edge_below (outgoing e)) low_e high_e = new_open_cells ->
s_right_form new_open_cells.
(*  && (head low_e [seq low c | c <- new_open_cells] == low_e). *)
Proof.
move=> pabove punder lowhigh outs alla allb noc new oe; apply/allP.
have sorted_e : sorted edge_below (sort edge_below (outgoing e)).
  have /sort_sorted_in : {in outgoing e &, total edge_below}.
    by move=> e1 e2 e1in e2in; apply/orP/noc.
  by apply;apply/allP=>x.
have /sub_in1 trsf : {subset sort edge_below (outgoing e) <= outgoing e}.
  move=> x.
  by rewrite (perm_mem (permEl (perm_sort edge_below (outgoing e)))).
move: new oe; move/trsf: allb; move/trsf: alla; move/trsf:outs.
move: sorted_e pabove punder lowhigh {trsf}.
elim: (sort edge_below (outgoing e)) low_e => [ | g1 edges IH] low_e
  sorted_e pabove punder lowhigh outs alla allb /=.
  case v_i_l_eq :
   (vertical_intersection_point (point e) low_e)=> [a1 | ];
   last by move=> s <- c.
  case v_i_h_eq :
   (vertical_intersection_point (point e) high_e) => [a2 | ];
   last by move=> s <- c.
  by case: ifP => [a2e | a2ne];
    case: ifP => [a1e | a1ne] s <- c;
     rewrite inE ?eqxx => /eqP ->;
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
  (apply: IH=> //); (try exact g1belowhigh); (try exact paboveg1); move=> //.
Qed.

(*
Lemma order_cells_viz_point (cells : seq cell) p :
forall c, c \in cells ->
valid_edge (low c) p -> valid_edge (high c) p ->
right_form c ->
p <<= (low c) ->  p <<= (high c).
Proof.

*)


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
have rfc1 : (right_form c1).
  move : op_rf.
  rewrite /s_right_form .
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
  by move: op_rf=> /allP /(_ c); rewrite inE eqxx /right_form => /(_ isT).
have underhigh : p <<= (high_c).
  rewrite (_ : high_c = high c); last by rewrite ceq.
  by apply: order_edges_viz_point.
have strictunder : p <<< (low c).
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
opening_cells (point e) (sort edge_below (outgoing e))
   low_e high_e = new_open_cells ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
(low (head dummy_cell new_open_cells) == low_e).
Proof.
case : (sort edge_below (outgoing e)) => [/= |/= c q] newop.
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

Lemma outleft_event_sort e :
  out_left_event e ->
  forall ed, ed \in sort edge_below (outgoing e) -> left_pt ed == point e.
Proof.
move=> outleft ed edin; apply: outleft.
by have <- := perm_mem (permEl (perm_sort edge_below (outgoing e))).
Qed.

Lemma higher_edge_new_cells e low_e high_e:
out_left_event e ->
forall new_open_cells,
opening_cells (point e) (sort edge_below (outgoing e)) low_e high_e =
   new_open_cells ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
(high (last dummy_cell new_open_cells) == high_e).
Proof.
move /outleft_event_sort.
elim : (sort edge_below (outgoing e)) low_e =>
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
move : lowunder cont  => /negP /= -> /= /negbT phc0.
have phc := negP (underWC phc0  ).
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
rewrite eqxx adjqhc0 /= => exis /andP [] /andP [] puepb puept _.
have /negP puespb := (underWC puepb).
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

Lemma close_out_from_event_sort event future :
  close_out_from_event event future ->
  all (end_edge^~ future) (sort edge_below (outgoing event)).
Proof.
move/allP=> outP; apply/allP=> x xin; apply outP.
by have <- := perm_mem (permEl (perm_sort edge_below (outgoing event))).
Qed.

Lemma opening_cells_close event low_e high_e future :
end_edge low_e future -> end_edge high_e future -> close_out_from_event event future ->
close_alive_edges (opening_cells (point event)
  (sort edge_below (outgoing event)) low_e high_e) future.
Proof.
move=> A B /close_out_from_event_sort; move: A B.
move : low_e high_e.
elim : (sort edge_below (outgoing event)) => [ | e0 q Ho].
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
rewrite /right_form /= => /andP [] linfh _.
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
~ (p <<< low_f) /\ (p <<= high_f).
Proof.
case : open  => [//=| c q ] cbtop adjopen insbox opval fc cc lc lowf highf.
have := exists_cell cbtop adjopen insbox => [][]c' []cin cont.
have exi : (exists c0 : cell, (c0 \in c :: q) && contains_point p c0).
  exists c'.
  by rewrite cin cont.
rewrite /open_cells_decomposition => op_f. 
have := (l_h_above_under_fix exi op_f) => /andP [] /negP.
by [].
Qed. 

Lemma l_under open p :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
seq_valid open p ->
s_right_form open ->
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition open p  = (first_cells, contact, last_cells, low_f, high_f) ->
~ (p <<= low_f).
Proof.
move => cbtop adjopen insboxp valopen r_f first_cells contact last_cells low_f high_f op_c.
have := decomposition_preserve_cells op_c.
have exi := exists_cell cbtop adjopen insboxp.
have := (l_h_c_decomposition op_c exi) => [][] low_eq [] _  cnnil.
case : contact op_c low_eq cnnil=> [// | c' q' /=] op_c /eqP low_eq _ .
rewrite -low_eq.
case : first_cells op_c => [/= | c q] op_c op_eq.
  move : cbtop.
  rewrite op_eq /cells_bottom_top /cells_low_e_top => /andP [] /andP [] _ /= /eqP -> _.
  move : insboxp.
  by rewrite /inside_box => /andP [] /andP  [] /negP.
move : (adjopen).
rewrite op_eq /=  adj_aux_path cat_path => /andP [] _ /= => /andP [] /eqP low_eq2 _.
rewrite -low_eq2.
have besb:= bottom_imp_seq_below cbtop insboxp.
have cin : ((last c q) \in c::q) || ((last c q) \in last_cells).
  by rewrite mem_last.
have := decomposition_not_contain r_f valopen adjopen besb op_c cin.
rewrite /contains_point => /negP .
rewrite negb_and => /orP [/negPn pinflow| /negP //].
move : (valopen).
rewrite /seq_valid op_eq all_cat => /andP [] /allP a _.
have := a (last c q).
rewrite mem_last => /( _ isT) /andP [] vallow valhigh.
move : r_f.
rewrite /s_right_form op_eq all_cat => /andP [] /allP b _.
have := b (last c q).
rewrite mem_last /right_form => /( _ isT) linfh.
have := l_h_above_under cbtop adjopen insboxp valopen op_c.
rewrite -low_eq -low_eq2 => [][] .
by rewrite (order_edges_strict_viz_point vallow valhigh linfh pinflow).
Qed.

Lemma h_above open p :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
seq_valid open p ->
s_right_form open ->
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition open p  = (first_cells, contact, last_cells, low_f, high_f) ->
 p <<< high_f.
Proof.
move => cbtop adjopen insboxp valopen r_f first_cells contact last_cells low_f high_f op_c.
have := decomposition_preserve_cells op_c.
have exi := exists_cell cbtop adjopen insboxp.
have := (l_h_c_decomposition op_c exi) => [][] _ [] high_eq  cnnil.
case : contact op_c high_eq cnnil=> [// | c' q' /=] op_c /eqP  high_eq _ .
rewrite -high_eq.
case : last_cells op_c => [/= | c q] op_c op_eq.
  move : cbtop.
  rewrite op_eq /cells_bottom_top /cells_low_e_top !last_cat cats0 => /andP [] /andP []  /=  _ _ /eqP ->.
  move : insboxp.
  by rewrite /inside_box => /andP [] /andP [].

have high_eq2:( high (last c' q') = low c).
  move : adjopen.
  
  case : first_cells op_c op_eq => [/= | c'' q'' ] op_c op_eq.
    by rewrite op_eq /adjacent_cells // adj_aux_path cat_path => /andP [] _ /= => /andP [] /eqP -> _.
  rewrite op_eq /adjacent_cells cat_cons  /= adj_aux_path cat_path => /andP [] _ /= /andP [] _.
  by rewrite cat_path => /andP [] _ /= => /andP[] /eqP .
rewrite high_eq2.

have besb:= bottom_imp_seq_below cbtop insboxp.
have cin : (c \in first_cells) || (c \in c::q).
  by rewrite inE eqxx orbT.
have := decomposition_not_contain r_f valopen adjopen besb op_c cin.
rewrite /contains_point => /negP .
rewrite negb_and => /orP [/negPn //| /negP //].
move : (valopen).
rewrite /seq_valid op_eq -cat_cons all_cat => /andP [] _ /allP .
move => /(_ c).
rewrite mem_cat !inE eqxx /= orbT  => /( _ isT) /andP [] vallow valhigh.
move : r_f.
rewrite /s_right_form op_eq -cat_cons all_cat => /andP [] _ /allP.
move => /(_ c).
rewrite mem_cat !inE eqxx /= orbT /right_form => /( _ isT) linfh.
have := l_h_above_under cbtop adjopen insboxp valopen op_c => [][] _.
rewrite -high_eq high_eq2 => pinflow. 
  by rewrite (order_edges_viz_point vallow valhigh linfh pinflow).
Qed.

Lemma l_h_above_under_strict open p :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
seq_valid open p ->
s_right_form open ->

forall first_cells contact last_cells low_f high_f,
open_cells_decomposition open p  = (first_cells, contact, last_cells, low_f, high_f) ->
~~ (p <<= low_f) && (p <<< high_f).
Proof.
move => cbtop adjopen insboxp openvalid r_f fc cc lc lf hf op_c.
have := l_under cbtop adjopen insboxp openvalid r_f op_c => /negP ->.
by rewrite (h_above cbtop adjopen insboxp openvalid r_f op_c).
Qed.

Lemma higher_lower_equality e open :
out_left_event e ->
forall first_cells contact_cells last_cells low_e high_e,
open_cells_decomposition open (point e) =
(first_cells, contact_cells, last_cells, low_e, high_e) ->
forall new_cells,
(opening_cells (point e) (sort edge_below (outgoing e)) low_e high_e) =
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
seq_valid (opening_cells (point e) (sort edge_below (outgoing e)) low_e high_e) (point e).
Proof.
move/outleft_event_sort.
move : low_e high_e.
elim out : (sort edge_below (outgoing e)) => [/= | c q IH] low_e high_e outl.
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
(opening_cells (point e) (sort edge_below (outgoing e)) low_e high_e) =
  open_cells ->
forall c , c\in open_cells ->
 ((left_pt (low c) == (point e)) || ((low c) == low_e) || ((low c) == high_e)) &&
 ((left_pt (high c) == (point e)) || ((high c) == low_e) || ((high c) == high_e)) .
Proof.
move/outleft_event_sort.
move : low_e high_e.
elim out : (sort edge_below (outgoing e)) => [/= | c q IH] low_e high_e outl.
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
(forall e', e' \in future -> lexePt p (point e')) ->
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
have := (open_not_nil (sort edge_below (outgoing e)) lowv highv).
case op_new : (opening_cells (point e) (sort edge_below (outgoing e))
   low_e high_e) => [//=| cnew q'' /=] _.
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
  by case : (fc).  
 
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
have := (open_not_nil (sort edge_below (outgoing e)) lowv highv).
case op_new : (opening_cells (point e) (sort edge_below (outgoing e)) low_e high_e) => [//= | cnew q'' /=] _.
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
opening_cells (point e) (sort edge_below (outgoing e)) low_e high_e =
  new_open_cells ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
adjacent_cells_aux new_open_cells low_e.
Proof.
move/outleft_event_sort.
elim : (sort edge_below (outgoing e)) low_e  =>
  [/= | ed q IH ] low_e outleft openc.
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
opening_cells (point e) (sort edge_below (outgoing e)) low_e high_e =
  new_open_cells ->
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
move => [] <- _ adjopen.
have exi := (exists_cell cbtop adjopen insbox ).
have openeq := decomposition_preserve_cells op_c_d.
have := (l_h_valid cbtop adjopen  insbox validopen op_c_d).
move => [] lowv highv.
have := (open_not_nil (sort edge_below (outgoing e)) lowv highv).
case op_new : (opening_cells (point e) (sort edge_below (outgoing e)) low_e high_e) => [//= | q l ] qlnnil.
have := higher_lower_equality outleft op_c_d op_new exi lowv highv => [][] l_eq [] h_eq c_nnil.
have := (adjacent_opening outleft op_new lowv highv) => adjnew.
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
move => [] <- _.
have := (l_h_valid cbtop adjopen insbox openvalid op_c_d).
move => [] lowv highv.
have exi := (exists_cell cbtop adjopen insbox ).
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top => /andP [] /andP [] opnnil /eqP openbottom /eqP _.
have newnnil := open_not_nil (sort edge_below (outgoing e)) lowv highv.
have newopnnil := (middle_seq_not_nil first_cells last_cells newnnil).
rewrite newopnnil /=.
case op_new : (opening_cells (point e) (sort edge_below (outgoing e))
   low_e high_e) => [// | c q].
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
have newnnil := open_not_nil (sort edge_below (outgoing e)) lowv highv.
have newopnnil := (middle_seq_not_nil first_cells last_cells newnnil).
case op_new : (opening_cells (point e) (sort edge_below (outgoing e)) low_e high_e) => [// | c q].
  by rewrite op_new in newnnil.
have := higher_lower_equality outleft op_c_d op_new exi lowv highv => [][] _ [] /= h_eq c_nnil.
case : last_cells op_c_d op_dec newopnnil => [/= op_c_d |c1 q1 _ op_dec /=]  .
  rewrite !cats0 -opentop last_cat  => -> newn_nil /=.
  rewrite last_cat -h_eq.
  by case  : contact_cells c_nnil h_eq op_c_d.
by rewrite -opentop op_dec !last_cat /= last_cat.
Qed.

Lemma order_below_viz_vertical low_e high_e p pl ph:
valid_edge low_e p -> valid_edge high_e p ->
vertical_intersection_point p low_e = Some pl ->
vertical_intersection_point p high_e = Some ph ->
low_e <| high_e ->
p_y pl <= p_y ph.
Proof.
move => lowv highv vert_pl vert_ph luh.
have := intersection_on_edge vert_pl => [][] poel lx_eq.
have := intersection_on_edge vert_ph => [][] poeh hx_eq.
have plhv: valid_edge high_e pl.
  move : highv.
  by rewrite /valid_edge -lx_eq.
have pllv: valid_edge low_e pl.
  move : lowv.
  by rewrite /valid_edge -lx_eq.
have := order_edges_viz_point' pllv  plhv luh.
rewrite under_onVstrict // poel /= => [] /= plinfh.
have pluh: pl <<= high_e .
  by apply plinfh.
have px_eq : p_x pl = p_x ph.
  by rewrite -lx_eq -hx_eq /=.
have := point_valid_under_imp_y_inf pluh poeh px_eq.
by rewrite subr_cp0.

Qed.

Definition no_crossing'  : Prop:=
 forall e e',
 valid_edge e (left_pt e') ->
(left_pt e' <<< e  -> e' <| e)  /\
(~ (left_pt e' <<= e)  -> e <| e').

Lemma no_crossingE e1 e2 :
  below_alt e1 e2 -> valid_edge e2 (left_pt e1) ->
  (left_pt e1 <<< e2 -> e1 <| e2) /\ (~~(left_pt e1 <<= e2) -> e2 <| e1).
Proof.
move=> nc ve.
case: (exists_point_valid ve) => [p pP].
move: (intersection_on_edge pP)=> [pone2 px].
move: (pone2); rewrite /point_on_edge=> /andP[] pone2' vp.
have xbnd1 : p_x (left_pt e2) <= p_x (left_pt e1) by case/andP: ve.
have xbnd2 : p_x (left_pt e1) <= p_x (right_pt e2) by case/andP: ve.
have dify : ((left_pt e1 <<< e2) \/ (~~(left_pt e1 <<= e2))) -> p_y (left_pt e1) != p_y p.
  move=> disj; apply/negP=> /eqP A.
  have {A}-A : p = left_pt e1 by case: (p) (left_pt e1) px A=> [? ?][? ?]/= -> ->.
  by move: disj; rewrite under_onVstrict // strict_nonAunder // -A pone2; case.
have pone2'': pue_f (p_x (left_pt e2)) (p_y (left_pt e2))
             (p_x (right_pt e2)) (p_y (right_pt e2))
             (p_x p) (p_y p) == 0.
  by rewrite -pue_f_c; move: pone2'; rewrite pue_formulaE pue_f_c.
move: (edge_cond e2); rewrite -(subr_gt0 (p_x _))=> ce2.
have dife2 : 0 < p_x (right_pt e2) - p_x (left_pt e2).
  by move: (edge_cond e2); rewrite -(subr_gt0 (p_x _)).
have dife2' : p_x (right_pt e2) - p_x (left_pt e2) != 0.
  by move: dife2; rewrite  lt_neqAle eq_sym=> /andP[].
have plp2 : p_x (left_pt e2) = p_x (left_pt e1) -> p = left_pt e2.
  move=> c; have:= on_edge_same_point pone2 (left_on_edge _).
  rewrite c px eqxx=> /(_ isT)=> /eqP; move: px c.
  by case: (p) (left_pt e2)=> [? ?][? ?]/= <- <- ->.
have prp2 : p_x (right_pt e2) = p_x (left_pt e1) -> p = right_pt e2.
  move=> c; have:= on_edge_same_point pone2 (right_on_edge _).
  rewrite c px eqxx=> /(_ isT)=> /eqP; move: px c.
  by case: (p) (right_pt e2)=> [? ?][? ?]/= <- <- ->.
have main : (0 < pue_formula (left_pt e1) (left_pt e2) (right_pt e2)) =
       (p_y p < p_y (left_pt e1)).
  move: xbnd1; rewrite le_eqVlt=> /orP[/eqP atleft | notleft ].
    have pisl : p = left_pt e2 by apply: plp2.
    move: atleft; rewrite -pisl=> atleft; rewrite edge_and_left_vertical //.
    by rewrite -atleft pisl (edge_cond e2).
  move: pone2'; rewrite -pue_formula_cycle=> pone2'.
  have fact1 : (0 < p_x p - p_x (left_pt e2)) by rewrite subr_gt0 -px.
  rewrite -(pmulr_rgt0 _ fact1) pue_formula_opposite -pue_formula_cycle mulrN.
  rewrite -(eqP (pue_formula_triangle_on_edge (left_pt e1) pone2')) -mulrN.
  rewrite -pue_formula_opposite pmulr_rgt0 //.
  by apply: edge_and_right_vertical; rewrite -px.
move: pone2'; rewrite -pue_formula_cycle=> pone2'.
have arith : forall (a b : rat), a <= 0 -> b <= 0 -> a + b <= 0.
  clear=> a b al0 bl0.
  by rewrite -ler_subr_addr (le_trans al0) // ler_subr_addr add0r.
have case1 : left_pt e1 <<< e2 -> e1 <| e2.
  move=> below; case:(nc) => // /orP[]; last by rewrite below.
  move/andP=> []le2b re2b.
  have pyne1 : p_y (left_pt e1) != p_y p by apply: dify; left.
  have ys : p_y (left_pt e1) < p_y p.
    rewrite ltNge le_eqVlt -main negb_or eq_sym pyne1 /= -leNgt le_eqVlt.
    by move: (below); rewrite /point_strictly_under_edge orbC => ->.
  have : 0 < pue_formula p (left_pt e1) (right_pt e1).
    by rewrite edge_and_left_vertical // -px (edge_cond e1).
  rewrite -(pmulr_rgt0 _ ce2) -pue_formula_cycle.
  rewrite (eqP (pue_formula_on_edge (left_pt e1) (right_pt e1) pone2')).
  rewrite ltNge arith //.
    apply: mulr_ge0_le0; first by rewrite -px subr_ge0.
    by move: re2b; rewrite /point_under_edge -pue_formula_cycle.
  apply: mulr_ge0_le0; first by rewrite -px subr_ge0.
  by move: le2b; rewrite /point_under_edge -pue_formula_cycle.
have case2 : ~~(left_pt e1 <<= e2) -> e2 <| e1.
  move=> above; case: (nc) => // /orP[]; first by rewrite (negbTE above).
  rewrite /point_strictly_under_edge -!leNgt => /andP[] le2a re2a.
  have pyne1 : p_y (left_pt e1) != p_y p by apply: dify; right.
  have ys : p_y p < p_y (left_pt e1).
    by rewrite -main;move: (above); rewrite /point_under_edge -ltNge.
  have : 0 < pue_formula (left_pt e1) p (right_pt e1).
    by rewrite edge_and_left_vertical // (edge_cond e1).
  rewrite pue_formula_opposite pue_formula_cycle.
  rewrite -(pmulr_rgt0 _ dife2) mulrN.
  move: (eqP (pue_formula_on_edge (left_pt e1) (right_pt e1) pone2')) => ->.
  rewrite oppr_gt0 ltNge addr_ge0 //.
    apply: mulr_ge0; first by rewrite -px subr_ge0.
    by rewrite pue_formula_cycle.
  apply: mulr_ge0; first by rewrite -px subr_ge0.
  by rewrite pue_formula_cycle.
by [].
Qed.

Lemma inter_at_ext_no_crossing (s : seq edge) :
  {in s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s &, no_crossing}.
Proof.
move=> nc e1 e2 e1in e2in.
have nc' := inter_at_ext_sym nc.
have ceq : e1 = e2 -> below_alt e1 e2.
  move=> <-; left; apply/orP; left; rewrite /point_under_edge.
  rewrite (fun a b => eqP (proj1 (pue_formula_two_points a b))).
  rewrite (fun a b => eqP (proj1 (proj2 (pue_formula_two_points a b)))).
  by rewrite lexx.
have [/eqP/ceq // | e1ne2] := boolP(e1 == e2).
have [/eqP | {nc}nc ] := nc _ _ e1in e2in; first by rewrite (negbTE e1ne2).
have [/eqP | {nc'}nc' ] := nc' _ _ e1in e2in; first by rewrite (negbTE e1ne2).
have [ | ] := boolP(e1 <| e2); first by left.
rewrite /edge_below; rewrite negb_or !negb_and !negbK.
have [le1u /= | le1a /=] := boolP (left_pt e1 <<= e2).
  have [re1u //= | re1a /=] := boolP (right_pt e1 <<= e2).
  move=>/orP[le2u | re2u].
    have [re2u | re2a] := boolP(right_pt e2 <<= e1).
      by right; rewrite /edge_below re2u underW.
    move: le1u; rewrite /point_under_edge le_eqVlt => /orP[le1on | ].
      have [u | a] := boolP(right_pt e1 <<< e2).
        left; rewrite /edge_below; apply/orP; left.
        by rewrite [in X in X && _]/point_under_edge (eqP le1on) lexx /= underW.
      right; rewrite /edge_below; apply/orP; right; rewrite a.
      by rewrite /point_strictly_under_edge (eqP le1on) ltxx.
    rewrite -[X in is_true X -> _]/(left_pt e1 <<< e2) => e1u.
    have [u | a] := boolP(right_pt e1 <<= e2).
      by left; apply/orP; left; rewrite u underW.

Lemma opening_cells_left e low_e high_e c :
out_left_event e ->
~~(point e <<< low_e) -> point e <<< high_e ->
valid_edge low_e (point e)-> valid_edge high_e (point e) ->
{in  (rcons (low_e::(sort edge_below (outgoing e))) high_e) &, no_crossing} ->
low_e <| high_e ->
 c \in (opening_cells (point e) (sort edge_below (outgoing e)) low_e high_e) ->
 lexePt (last dummy_pt (left_pts c)) (point e).
Proof.
move => /outleft_event_sort outlefte eabl eunh lowv highv .

elim : (sort edge_below (outgoing e)) low_e eabl lowv outlefte => [/= | c' q IH] low_e eabl lowv outlefte nc linfh.
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
  have := point_valid_above_imp_y_inf eabl poel lx_eq.
  rewrite subr_cp0 => ->.
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
have outq: (forall e0 : edge_eqType, e0 \in q -> left_pt e0 == point e).
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
have nc' : {in  (rcons (c'::q) high_e) &, no_crossing}.
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
  have := point_valid_above_imp_y_inf eabl poel lx_eq.
  rewrite /lexePt subr_cp0 lx_eq eqxx=> ->.
  by rewrite orbT.
apply : (IH c' einfc' c'v outq nc' c'infh).
Qed.

Lemma open_cells_decomposition_low_under_high open p fc cc lc le he:
  {in [seq low c | c <- open] ++ [seq high c | c <- open] &, no_crossing} ->
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
have /andP[/negP e1 e2]:= l_h_above_under_strict cbtom adj insp valp r_f op_c_d_eq.
have vl : valid_edge le p.
  by move: valp; rewrite /seq_valid=>/allP/(_ _ lcin)/andP[]; rewrite le_eq.
have vh : valid_edge he p.
  by move: valp; rewrite /seq_valid=>/allP/(_ _ hcin)/andP[]; rewrite he_eq.
case: e1; have := (order_edges_strict_viz_point' vh vl abs_he_under_le e2).
apply underW.
Qed.

Lemma lexePt_xW p1 p2 : lexePt p1 p2 -> p_x p1 <= p_x p2.
Proof.
by rewrite /lexePt=> /orP[/ltW | /andP [/eqP -> _]].
Qed.

Lemma step_keeps_left_pts_inf e (future_events : seq event) p old_open : 
inside_box (point e) -> out_left_event e ->
s_right_form old_open -> seq_valid old_open (point e) ->
adjacent_cells old_open -> cells_bottom_top old_open ->
close_alive_edges old_open (e :: future_events) ->
close_edges_from_events (e :: future_events) ->
{in  ((map low old_open) ++ (map high old_open) ++ flatten (map outgoing (e::future_events))) &, no_crossing} ->
(forall c, c \in old_open -> p_x (last dummy_pt (left_pts c)) <= p_x (point e)) ->
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
have := l_h_above_under_strict cbtom adjopen insboxe openval srf op_c_d => /andP [lowinfe einfhigh].
have [vallow valhigh]:= l_h_valid cbtom adjopen insboxe openval op_c_d.
have linfh : low_e <| high_e.
  have n_c' : {in [seq low i | i <- old_open] ++ [seq high i | i <- old_open] &,
                 no_crossing}.
    have sub_cat (s1 s2 : seq edge): forall x, x \in s1 -> x \in s1 ++ s2.
      by move=> x; rewrite mem_cat => ->.
    by move: n_c; rewrite catA=> /(sub_in2 (sub_cat _ _)).
  by apply: open_cells_decomposition_low_under_high _ _ _ _ _ op_c_d.
have n_c' : {in rcons (low_e :: sort edge_below (outgoing e)) high_e &, no_crossing}.
  have [lc1 [lc2 [lc1in [lc2in]]]] := l_h_in_open cbtom adjopen insboxe.
    rewrite op_c_d /= => [][lowlc1 highlc2].
  have subseq:
    forall x, x \in rcons (low_e :: sort edge_below (outgoing e)) high_e ->
          x \in ([seq low i | i <- old_open] ++
            [seq high i | i <- old_open] ++
            flatten [seq outgoing i | i <- e :: future_events]).
    move=> x; rewrite -cats1 mem_cat 2!inE 2!mem_cat orbAC=> /orP[].
      by move=>/orP[]/eqP ->; rewrite -?lowlc1 -?highlc2 map_f ?orbT.
    rewrite mem_sort orbA=> xin; apply/orP; right.
    by apply/flattenP; exists (outgoing e); rewrite // inE eqxx.
  by apply: (sub_in2 subseq).
have lowinfe' : ~~ (point e <<< low_e).
  move : lowinfe => lowinfe.
  apply (underWC lowinfe).
have cinfe := (opening_cells_left outlefte lowinfe' einfhigh vallow valhigh n_c' linfh cin).
by apply/(le_trans (lexePt_xW cinfe))/lexePt_xW/lexPtW.
Qed.

Lemma step_keeps_right_form e open closed op2 cl2 :
  cells_bottom_top open -> adjacent_cells open -> 
  inside_box (point e) -> seq_valid open (point e) ->
  {in [seq low c | c <- open] ++ [seq high c | c <- open] ++
      outgoing e &, no_crossing} ->
  out_left_event e ->
  s_right_form open ->
  step e open closed = (op2, cl2) ->
  s_right_form op2.
Proof.
move=> cbtom adj inbox_e sval noc oute rfo; rewrite /step /=.
case oe : (open_cells_decomposition open (point e)) => [[[[fc cc] lc] le] he].
move=> [] <- _.
have ocd := decomposition_preserve_cells oe.
have oute': {in outgoing e, forall g, left_pt g = point e}.
  by move=> x xin; apply/eqP/oute.
have/andP[lP hP] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have [c1 [c2 [c1in [c2in]]]] := l_h_in_open cbtom adj inbox_e.
rewrite oe /= => [][le_eq he_eq].
have lein : le \in [seq low c | c <- open] by rewrite -le_eq map_f.
have hein : he \in [seq high c | c <- open] by rewrite -he_eq map_f.
have lev : valid_edge le (point e) by have [] := l_h_valid _ _ _ _ oe.
have hev : valid_edge he (point e) by have [] := l_h_valid _ _ _ _ oe.
have /andP[leP heP ] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have edgesabove : {in outgoing e, forall g, le <| g}.
  move=> g gin; have := noc g le; rewrite !mem_cat gin lein !orbT /=.
  move=> /(_ isT isT)/no_crossingE[]; first by rewrite oute'.
  by move=> _; apply; rewrite oute'.
have edgesbelow : {in outgoing e, forall g, g <| he}.
  move=> g gin; have := noc g he; rewrite !mem_cat gin hein !orbT /=.
  move=> /(_ isT isT)/no_crossingE[]; first by rewrite oute'.
  by move=> + _; apply; rewrite oute'.
have /allP rfn : s_right_form 
    (opening_cells (point e) (sort edge_below (outgoing e)) le he).
  apply: (opening_cells_right_form (underWC leP) heP) => //.
    apply: (open_cells_decomposition_low_under_high _ _ _ _ _ _ oe) => //.
    by move: noc; apply: sub_in2=> x xin; rewrite catA mem_cat xin.
  by move: noc; apply: sub_in2=> x xin; rewrite !mem_cat xin !orbT.
apply/allP=> x; rewrite !mem_cat orbCA=> /orP[/rfn// | ].
by move=> xin; apply: (allP rfo); rewrite ocd !mem_cat orbCA xin orbT.
Qed.

Lemma size_open_ok (p : pt) (out : seq edge) (low_e : edge) (high_e : edge) :
valid_edge low_e p ->
valid_edge high_e p ->
(forall e, e \in out -> left_pt e == p) ->
let open :=  opening_cells p out low_e high_e in
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

Lemma opening_cells_subset c p s le he:
  c \in opening_cells p s le he ->
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

(* This will be necessary to prove that the no_crossing property is preserved. *)
Lemma step_edges_open_subset e open closed open' closed' :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  step e open closed = (open', closed') ->
  {subset map low open' ++ map high open' <=
    outgoing e ++ map low open ++ map high open}.
Proof.
move=> cbtom adj insbox_e; rewrite /step /=.
case oe: (open_cells_decomposition open (point e)) => [[[[fc cc] lc] le] he] [].
have dcp := decomposition_preserve_cells oe.
have new c p : c \in opening_cells p (sort edge_below (outgoing e)) le he ->
  let w := outgoing e ++ [seq low i | i <- open] ++ [seq high i | i <- open] in
  (low c \in w) && (high c \in w).
  move/opening_cells_subset; rewrite !inE=> /andP[lcond hcond] /=.
  have [c1 [c2]] := l_h_in_open cbtom adj insbox_e.
  rewrite oe /= => [][c1in [c2in [le_eq he_eq]]].
  apply/andP; split; rewrite !mem_cat.
    case/orP: lcond=> [/eqP -> |];[ | rewrite mem_sort=> -> //].
    by rewrite -le_eq map_f ?orbT.
  case/orP: hcond=> [/eqP -> |];[ | rewrite mem_sort=> -> //].
  by rewrite -he_eq map_f ?orbT.
move=> <- _ x; rewrite mem_cat=> /orP[/mapP[c + ->] | /mapP[c + ->]];
  (rewrite 2!mem_cat orbCA orbC => /orP[cold | /new /andP[] // ];
   rewrite 2!mem_cat dcp orbC  map_f ?orbT // 2!mem_cat orbCA cold orbT//).
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
  have [pbot ptop] : p_x p <= p_x (right_pt bottom) /\
             p_x p <= p_x (right_pt top).
    by apply/andP; move:inbox_p=> /andP[] _ /andP[] /andP[] _ -> /andP[] _ ->.
  move=>/orP[]; [by rewrite !inE => /orP[]/eqP -> | ].
  move/hasP=> [ev' ev'in /eqP ->].
  apply: lexePt_xW.
  by apply/(allP rightb)/map_f.
have /andP [cmp1 cmp2] : (p_x p <= p_x (right_pt (low c))) &&
                (p_x p <= p_x (right_pt (high c))).
  by apply/andP; split; apply/cledge; move/allP: clae=> /(_ _ cin)/andP[].
rewrite /right_limit.
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

Lemma step_keeps_cover e open closed open' closed' p evs :
  sorted lexPt [seq point x | x <- (e :: evs)] ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  out_left_event e ->
  s_right_form open ->
  close_alive_edges open (e :: evs) ->
  close_edges_from_events (e :: evs) ->
  {in [seq low i | i <- open] ++
       [seq high i | i <- open] ++ flatten [seq outgoing i | i <- e :: evs] &,
     no_crossing} ->
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
have inrest : forall CC c, c \in CC -> inside_open_cell q c ->
  (forall c, c \in CC -> valid_edge (low c) (point e) &&
     (valid_edge (high c) (point e))) ->
  exists2 c', c' \in closing_rest (point e) CC & inside_closed_cell q c'.
  elim => [// | c' cc' Ih] c.
  rewrite inE=> /orP[/eqP cisc' | cincc'] inq sval'.
    rewrite /=; case: cc' Ih sval' => [ | c2 cc'2] Ih sval'.
      have /exists_point_valid [p2 vp2] : valid_edge (high c') (point e).
        by have := sval' c'; rewrite inE eqxx => /(_ isT)/andP[].
      rewrite vp2; set c'' := (X in [:: X]); exists c''.
        by rewrite inE eqxx.
      rewrite /inside_closed_cell.
      case/andP: inq=> ctn /andP[liml _] /=.
      move: ctn; rewrite /contains_point /c'' /= cisc' => ->.
      have p2e : p_x p2 = p_x (point e).
        by have [_ ->] := intersection_on_edge vp2.
      by move: liml; rewrite cisc' => ->; case: ifP=> _ /=; rewrite p2e.
    set c'' := (X in X :: closing_rest _ _); exists c''.
      by rewrite inE eqxx.
    rewrite /inside_closed_cell.
    case/andP: inq=> ctn /andP[liml _] /=.
    move: ctn; rewrite /contains_point /c'' /= cisc' => ->.
    by rewrite -cisc' liml.
  have sval2 : forall c, c \in cc' ->
        valid_edge (low c) (point e) && valid_edge (high c) (point e).
    by move=> c0 c0in; apply sval'; rewrite inE c0in orbT.
  case: (Ih _ cincc' inq sval2)=> [c'' c''in insc'']; exists c''=> //.
  rewrite /=.
  by case: (cc') cincc' c''in => // [a l] _ it; rewrite inE it orbT.
have inclosing : forall c, c \in cc -> inside_open_cell q c ->
  (forall c, c \in cc -> valid_edge (low c) (point e) &&
     (valid_edge (high c) (point e))) ->
  exists2 c', c' \in closing_cells (point e) cc & inside_closed_cell q c'.
  case: (cc) => [// | c' cc'] c.
  rewrite inE=> /orP[/eqP cisc' | cincc'] inq sval'.
    rewrite /closing_cells; case: cc' sval' => [ | c2 cc'2] sval'.
      have /exists_point_valid [p2 vp2] : valid_edge (high c') (point e).
        by have := sval' c'; rewrite inE eqxx => /(_ isT)/andP[].
      have /exists_point_valid [p1 vp1] : valid_edge (low c') (point e).
        by have := sval' c'; rewrite inE eqxx => /(_ isT)/andP[].
      rewrite vp1 vp2; set c'' := (X in [:: X]); exists c''.
        by rewrite inE eqxx.
      rewrite /inside_closed_cell.
      case/andP: inq=> ctn /andP[liml _] /=.
      move: ctn; rewrite /contains_point /c'' /= cisc' => ->.
      by move: liml; rewrite cisc' (no_dup_seq_x3 _ vp2) => ->.
    have /exists_point_valid [p1 vp1] : valid_edge (low c') (point e).
      by have := sval' c'; rewrite inE eqxx => /(_ isT)/andP[].
    rewrite vp1 /=; set c'' := (X in X :: _).
    exists c''; first by rewrite inE eqxx.
    rewrite /inside_closed_cell.
    case/andP: inq=> ctn /andP[liml _] /=.
    move: ctn; rewrite /contains_point /c'' /= cisc' => ->.
    by move: liml; rewrite cisc' => ->; case: ifP=> _ /=.
  rewrite /closing_cells.
  case cc'eq: cc' => [  | a s] //; first by move: cincc'; rewrite cc'eq.
  have /exists_point_valid [p1 vp1] : valid_edge (low c') (point e).
    by have := sval' c'; rewrite inE eqxx => /(_ isT)/andP[].
  rewrite vp1 -cc'eq.
  have sval2 : forall c, c \in cc' ->
     valid_edge (low c) (point e) && valid_edge (high c) (point e).
    by move=> c0 c0in; apply sval'; rewrite inE c0in orbT.
  have [c'' c''in insc''] := inrest _ _ cincc' inq sval2.
  by exists c''=> //; rewrite inE c''in orbT.
clear inrest.
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

Definition cell_no s i := nth dummy_cell s i.

Definition disjoint_cells (s : seq cell) :
  forall i j, (i < j < size s)%N ->
   forall p, inside_open_cell p (cell_no s i) ->
             inside_open_cell p (cell_no s j) ->
             p === high (cell_no s i).

Lemma step_keeps_disjoint :


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
   sorted lexPt [seq point x | x <- edges_to_events s].
Proof.
have /mono_sorted -> : {mono point : x y / lexPtEv x y >-> lexPt x y} by [].
by elim: s => [ | g s Ih] //=; do 2 apply: add_event_sort.
Qed.

Lemma add_event_preserve_ends bottom top p e inc evs ed :
  end_edge bottom top ed evs ->
  end_edge bottom top ed (add_event p e inc evs).
Proof.
have [excp | norm ] := boolP(ed \in [:: top; bottom]).
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

(* Todo : most previous uses of flatten should be replaced by uses
  of events_to_edges *)
Definition events_to_edges := flatten \o (map outgoing).

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
  {in s &, no_crossing} ->
  {in events_to_edges (edges_to_events s) &, no_crossing}.
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
  have:= opening_cells_subset cin; rewrite inE => /andP[] /orP[/eqP -> | +] _. 
    by rewrite map_f ?orbT //.
  by rewrite (perm_mem (permEl (perm_sort _ _))) => ->; rewrite ?orbT.
move/mapP=> [c cin ->].
have:= opening_cells_subset cin; rewrite !inE => /andP[] _ /orP[/eqP -> | +].
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
    by apply: (le_trans pgelt).
  by rewrite p1P /=; move: (intersection_on_edge p1P)=>[] _ <-.
move/negbT: cmpl; rewrite -leNgt=>cmpl.
have /exists_point_valid [p1 p1P] : valid_edge top (left_pt bottom).
  rewrite /valid_edge cmpl /=.
  by apply: (le_trans pgelb).
by rewrite p1P /=.
Qed.
  
Lemma start_cover (bottom top : edge) (s : seq edge) closed open :
  bottom <| top ->
  {in bottom :: top :: s &, no_crossing} ->
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
have : sorted lexPt [seq point x | x <- evs].
  by apply: sorted_edges_to_events.
have : cells_bottom_top bottom top op0.
  by rewrite /op0/cells_bottom_top/cells_low_e_top/= !eqxx.
have : adjacent_cells op0 by [].
have : s_right_form op0 by rewrite /=/right_form/= boxwf.
have : close_alive_edges bottom top op0 evs.
  by rewrite /=/end_edge !inE !eqxx !orbT.
have : {in [seq low i | i <- op0] ++
       [seq high i | i <- op0] ++ 
       flatten [seq outgoing i | i <- evs] &,
     no_crossing}.
  rewrite /=; move: nocs; apply sub_in2.
  move=> x; rewrite !inE => /orP[-> //| [/orP[-> // | ]]]; rewrite ?orbT//.
  by rewrite -stoevs orbA orbC => ->.
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
  by move: evsin0; rewrite evseq /= => /andP[/andP[]].
have cov0 : forall p, all (lexePt p) [seq point ev | ev <- evs] ->
         cover_left_of bottom top p op0 cl0.
  move=> p limrp q inbox_q qp; apply/orP; left; apply/hasP.
  exists (Bcell (leftmost_points bottom top) nil bottom top).
    by rewrite /op0 inE eqxx.
  apply/andP; split;[apply/andP; split => /= | move=>/=].
  - by apply: underWC; move: inbox_q=> /andP[] /andP[].
  - by apply: underW; move: inbox_q=> /andP[] /andP[].
  - rewrite /right_limit /=.
    case: (ltrP  (p_x (right_pt bottom)) (p_x (right_pt top))) => _.
    rewrite inside_box_left_ptsP //.
    by  move: (inbox_q) => /andP[] _ /andP[] /andP[].
  rewrite inside_box_left_ptsP //.
  by  move: (inbox_q) => /andP[] _ /andP[] _ /andP[].
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
  move: sortev; rewrite /sorted /= (path_sortedE lexPt_trans) // => /andP[+ _].
  by apply: sub_all; exact: lexPtW.
have cov' : forall p : pt,
    all (lexePt p) [seq point ev0 | ev0 <- evs'] ->
    cover_left_of bottom top p op' cl'.
  have := step_keeps_cover sortev cbtom adj inbox_e sval' oute' rfo clae clev
           noc btm_left' stepeq cov.
  by [].
have evle : forall ev', ev' \in evs' -> lexPt (point ev) (point ev').
  move=> ev' ev'in.
  move: sortev=> /=; rewrite (path_sortedE lexPt_trans)=> /andP[]/allP.
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
have nocr : {in [seq low i | i <- op'] ++
       [seq high i | i <- op'] ++ flatten [seq outgoing i | i <- evs'] &,
     no_crossing}.
  move: noc; apply: sub_in2=> x.
  rewrite catA mem_cat=> /orP[].
    move/(step_sub_open_edges cbtom adj inbox_e stepeq)=> it.
    by rewrite /= 2!catA -(catA _ _ (outgoing ev)) mem_cat it.
  by move=> xinf; rewrite /= !mem_cat xinf !orbT.
have claer : close_alive_edges bottom top op' evs'.
  by have := step_keeps_closeness inbox_e oute' rfo cbtom adj sval' clev
      clae stepeq.
have rfor : s_right_form op'.
  have noc1: {in [seq low c | c <- op] ++ [seq high c | c <- op] ++
         outgoing ev &, no_crossing}.
    move: noc; apply sub_in2=> x.
    rewrite catA mem_cat=> /orP[it| xino].
      by rewrite /= 2!catA 2!mem_cat it.
    by rewrite /= !mem_cat xino !orbT.
  by apply: (step_keeps_right_form cbtom adj inbox_e sval' noc1 _ _ stepeq).
have adjr : adjacent_cells op'.
  by have := step_keeps_adjacent inbox_e oute' sval' cbtom stepeq adj.
have cbtomr : cells_bottom_top bottom top op'.
  by apply: (step_keeps_bottom_top inbox_e sval' adj cbtom oute' stepeq).
have sortev' : sorted lexPt [seq point x | x <- evs'].
  by move: sortev; rewrite /= => /path_sorted.
by have := Ih _ _ cov' evsinr svalr btm_leftr clevr outer nocr claer rfor adjr
        cbtomr sortev' scaneq.
Qed.
