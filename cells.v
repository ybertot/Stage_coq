
From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.

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

Lemma allcons [T : predArgType]
  (f : T -> bool) a q' : all f (a :: q') = f a && all f q'.
Proof.  by []. Qed.

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

Lemma pt_eqE p1 p2 : (p1 == p2) = (p_x p1 == p_x p2) && (p_y p1 == p_y p2).
Proof. by move: p1 p2 => [? ?][? ?]. Qed.

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

Notation "p '>>=' e" := (~~(point_strictly_under_edge p e))( at level 70, no associativity).
Notation "p '>>>' e" := (~~(point_under_edge p e))(at level 70, no associativity).

(*returns true if e1 is under e2*)

Definition compare_incoming (e1 e2 : edge) : bool :=
  let: Bedge a _ _ := e1 in
   a <<= e2.

(*returns true if e1 is under e2*)
Definition compare_outgoing (e1 e2 : edge) : bool :=
  let: Bedge _ b _ := e1 in
   b <<= e2.

(* Check @Bedge (Bpt 3%:Q 4%:Q) (Bpt 4%:Q 4%:Q) isT. *)

(* Compute compare_incoming  (@Bedge  (Bpt 2%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT) (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT ). *)


(* Compute compare_outgoing (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 1%:Q) isT ) (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT). *)

Definition sort_incoming (inc : seq edge) : seq edge :=
  sort compare_incoming inc.
Definition sort_outgoing (out : seq edge) : seq edge :=
  sort compare_outgoing out.


Definition E1 : edge := (@Bedge  (Bpt 2%:Q 5%:Q) (Bpt 3%:Q 3%:Q) isT).
Definition E2 : edge := (@Bedge  (Bpt (@Rat (7%:Z, 3%:Z) isT)  10%:Q) (Bpt 3%:Q 3%:Q) isT).
Definition E3 : edge := (@Bedge  (Bpt 1%:Q 1%:Q) (Bpt 3%:Q 3%:Q) isT).

Definition sorted_inc := map left_pt (sort_incoming [:: E1; E2; E3]).
(* Eval lazy in sorted_inc. *)

Definition E4 : edge := (@Bedge  (Bpt 2%:Q 3%:Q) (Bpt 4%:Q 6%:Q) isT).
Definition E5 : edge := (@Bedge  (Bpt 2%:Q 3%:Q) (Bpt 5%:Q 3%:Q) isT).
Definition E6 : edge := (@Bedge  (Bpt 2%:Q 3%:Q) (Bpt 4%:Q 3%:Q) isT).
Definition sorted_out := map right_pt (sort_outgoing [:: E4; E5; E6]).
(* Eval lazy in sorted_out. *)


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
pue_f  m_x m_y a_x a_y b_x b_y == 0 ->
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
pue_f  m_x m_y a_x a_y b_x b_y == 0 ->
(b_x - a_x) * pue_f m_x m_y c_x c_y d_x d_y ==
(m_x - a_x) * pue_f b_x b_y c_x c_y d_x d_y + (b_x - m_x) * pue_f a_x a_y c_x c_y d_x d_y.
Proof.
move => on_ed.
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_triangle_on_edge a_x a_y b_x b_y p_x p_y p'_x p'_y :
pue_f p'_x p'_y a_x a_y b_x b_y == 0 ->
(b_x - a_x) * pue_f p'_x p'_y a_x a_y p_x p_y ==
(p'_x - a_x) * pue_f b_x b_y a_x a_y p_x p_y .
Proof.
move=> on_ed.
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_triangle_on_edge' a_x a_y b_x b_y p_x p_y p'_x p'_y :
pue_f p'_x p'_y a_x a_y b_x b_y == 0 ->
(b_x - a_x) * pue_f p'_x p'_y p_x p_y b_x b_y ==
(b_x - p'_x) * pue_f a_x a_y p_x p_y b_x b_y .
Proof.
move => on_ed .
rewrite pue_f_linear /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_on_edge_same_point a_x a_y b_x b_y p_x p_y p_x' p_y':
a_x != b_x ->
pue_f p_x p_y a_x a_y b_x b_y == 0 ->
pue_f p_x' p_y' a_x a_y b_x b_y == 0 ->
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
  c_x != d_x ->
  0 < pue_f c_x c_y a_x a_y b_x b_y ->
  pue_f  d_x d_y a_x a_y b_x b_y < 0 ->
  exists p_x p_y,
    pue_f p_x p_y a_x a_y b_x b_y = 0 /\
    pue_f p_x p_y c_x c_y d_x d_y = 0 /\
    (forall q_x q_y, pue_f q_x q_y a_x a_y b_x b_y = 0 ->
       pue_f q_x q_y c_x c_y d_x d_y = 0 -> p_x = q_x /\ p_y = q_y).
Proof.
move=> cltd cabove cunder.
set A := a_y - b_y; set B := b_x - a_x; set C := \det(mkmx2 a_x a_y b_x b_y).
have puef1_id x y : pue_f x y a_x a_y b_x b_y = A * x + B * y + C.
  by rewrite /A /B /C det_mkmx2 /pue_f; mc_ring.
set D := c_y - d_y; set E := d_x - c_x; set F := \det(mkmx2 c_x c_y d_x d_y).
have puef2_id x y : pue_f x y c_x c_y d_x d_y = D * x + E * y + F.
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
set sol := - (M ^-1 *m mkcv2 C F) : 'cV_2.
have soleq : sol = mkcv2 (sol ord0 ord0) (sol ord_max ord0).
  apply/matrixP=> [][[ | [ | i]]] // ip [ [ | j]] // jp; rewrite /= !mxE /=;
    (rewrite (_ : Ordinal jp = ord0); last apply: val_inj=> //).
    by rewrite (_ : Ordinal ip = ord0); last apply: val_inj.
  by rewrite (_ : Ordinal ip = ord_max); last apply: val_inj.
have detm : \det M != 0.
  have dets : \det M = A * E - D * B.
    rewrite (expand_det_col _ ord0) big_ord_recr /= big_ord1 !mxE /= /cofactor.
    by rewrite !det_mx11 /= expr1 expr0 !mulNr !mulrN !mul1r !mxE.
  have -> : \det M = pue_f d_x d_y a_x a_y b_x b_y -
                  pue_f c_x c_y a_x a_y b_x b_y.
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
suff/matrixP mq : mkcv2 qx qy = sol.
  by split; rewrite -?(mq ord0 ord0) -?(mq ord_max ord0) mxE.
by rewrite /sol -mulmxN solmq mulKmx.
Qed.

Lemma pue_f_eq_slopes ax ay bx b_y mx my :
  pue_f  mx my ax ay bx b_y =
   (my - ay) * (bx - ax) - (mx - ax) * (b_y - ay) /\
  pue_f  mx my ax ay bx b_y =
   -((b_y - my) * (bx - ax) - (bx - mx) * (b_y - ay)).
Proof.
split; rewrite /pue_f; mc_ring.
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
pue_formula m a b == 0 ->
(p_x b - p_x a) * pue_formula m c d ==
(p_x m - p_x a) * pue_formula b c d + (p_x b - p_x m) * pue_formula a c d.
Proof.
move : a b c d m => [ax ay] [b_x b_y] [cx cy] [dx dy] [mx my]/=.
apply pue_f_on_edge.
Qed.

Lemma pue_formula_on_edge_y a b m :
pue_formula m a b == 0 ->
(p_x b - p_x a) * p_y m = p_x m * (p_y b - p_y a) - (p_x a * p_y b - p_x b * p_y a).
Proof.
move : a b m => [ax ay] [b_x b_y]  [mx my]/=.
apply pue_f_on_edge_y.
Qed.

Lemma pue_formula_triangle_on_edge a b p p' :
pue_formula p' a b == 0 ->
(p_x b - p_x a) * pue_formula p' a p ==
(p_x p' - p_x a) * pue_formula b a p.
Proof.
move : a b p p' => [ax ay] [b_x b_y] [px py] [p'x p'y] /=.
apply pue_f_triangle_on_edge.
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

Definition valid_edge e p := p_x (left_pt e) <= p_x p <= p_x (right_pt e).

Lemma valid_edge_extremities e0 p:
(left_pt e0 == p) || (right_pt e0 == p) ->
valid_edge e0 p.
Proof.
rewrite /valid_edge.
by move => /orP [/eqP eq |/eqP eq ];
rewrite -eq lexx ?andbT /= {eq} ltW // ; case : e0 .
Qed.

Definition valid_cell c x := (valid_edge (low c) x) /\ (valid_edge (high c) x).


Definition point_on_edge (p: pt) (e :edge) : bool :=
  (pue_formula p (left_pt e) (right_pt e) == 0) && (valid_edge e p).

Notation "p '===' e" := (point_on_edge p e)( at level 70, no associativity).

Definition edge_below (e1 : edge) (e2 : edge) : bool :=
((left_pt e1 <<= e2) && (right_pt e1 <<= e2))
|| (~~  (left_pt e2 <<< e1) && ~~ (right_pt e2<<< e1)).

Notation "e1 '<|' e2" := (edge_below e1 e2)( at level 70, no associativity).

Definition below_alt (e1 : edge) (e2 : edge) :=
  edge_below e1 e2 \/ edge_below e2 e1.

Lemma edge_below_refl e : e <| e.
Proof.
apply/orP; left; rewrite /point_under_edge.
rewrite (eqP (proj1 (pue_formula_two_points _ _))).
by rewrite (eqP (proj1 (proj2 (pue_formula_two_points _ _)))) lexx.
Qed.

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

Definition right_form (c : cell) : bool := low c <| high c.

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
~~ (left_pt high_e <<< low_e) ->
~~ (right_pt high_e <<< low_e) ->
~~ (a <<< low_e).
Proof.
move : high_e => [lr hr inH] /=.
rewrite /point_on_edge /valid_edge => /andP [] /= poea /andP [] linfa ainfr.
have pf := pue_formula_on_edge (left_pt low_e) (right_pt low_e) poea.
rewrite /point_strictly_under_edge -!leNgt => llrllh llrllrh.
have diffa : (p_x lr - p_x a) <= 0.
  by rewrite subr_cp0.
have diffb : (p_x hr - p_x a) >= 0.
  by rewrite subr_cp0.
have difflh : (p_x lr - p_x hr) < 0.
  by rewrite subr_cp0.
rewrite -(ler_nmul2l difflh _ 0) mulr0 -opprB mulNr oppr_le0 (eqP pf).
by rewrite addr_ge0 // mulr_ge0 // subr_ge0.
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
rewrite /point_under_edge => llrllh llrllrh.
have diffa : (p_x lr - p_x a) <= 0.
  by rewrite subr_cp0.
have diffb : (p_x hr - p_x a) >= 0.
  by rewrite subr_cp0.
have difflh : (p_x lr - p_x hr) < 0.
  by rewrite subr_cp0.
rewrite -(ler_nmul2r difflh 0 _) mul0r mulrC -opprB mulNr (eqP pf) opprD.
by rewrite addr_ge0 // -mulNr mulr_le0 // oppr_le0 subr_cp0.
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

Lemma under_above_on e p :
  valid_edge e p -> p <<= e -> p >>= e -> p === e.
Proof.
move=> v u a; apply/andP; split => //.
apply/eqP/le_anti/andP;split; [assumption | rewrite leNgt; assumption].
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

Lemma psue_right_edge e p :
p_x (right_pt e) == p_x p ->
(p <<< e) = ((p_y p - p_y (right_pt e)) < 0).
Proof.
move : e p  => [[ax ay][bx b_y] /= cnd] [px py]  /=.
rewrite /point_strictly_under_edge /=.
move => /eqP <- /=.
have := (pue_f_vert py ax ay bx b_y).
rewrite pue_f_c /pue_f.
move => /eqP ->.
rewrite -subr_gt0 in cnd.
by rewrite (pmulr_rlt0 _  cnd) .
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

Lemma psue_left_edge e p :
p_x (left_pt e) == p_x p ->
(p <<< e) = (0 < p_y (left_pt e) - p_y p).
Proof.
move: e p => [[ax ay][bx b_y] /= cnd] [px py] /=.
move=> /eqP <- /=.
rewrite /point_strictly_under_edge /=.
have := (pue_f_vert ay bx b_y ax py).
rewrite -pue_f_c /pue_f => /eqP ->.
rewrite -subr_cp0 in cnd.
by rewrite (nmulr_rlt0 _ cnd).
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
move : e => [l r ec].
rewrite /point_on_edge /= => /andP [] p0 _ /andP[] p'0 _.
have dif : p_x l != p_x r.
  by apply/eqP=> abs; move: ec; rewrite abs ltxx.
move: l r p0 p'0 dif {ec}=> [a_x a_y][b_x b_y] p0 p'0 dif.
move: p p' p0 p'0 => [x y] [x' y'] puep0 puep'0.
rewrite /=; apply: (pue_f_on_edge_same_point dif puep0 puep'0).
Qed.

Lemma strict_under_edge_lower_y r r' e :
  p_x r = p_x r' -> r' === e -> (r <<< e) = (p_y r < p_y r').
Proof.
move=> rr' rone.
have valre : valid_edge e r by case/andP: rone; rewrite /valid_edge rr'.
move: (valre)=> /andP[] + _; rewrite le_eqVlt=> /orP[/eqP atl| inr].
  have req : r' = left_pt e.
    have rltr : p_x r' < p_x (right_pt e) by rewrite -rr' -atl edge_cond.
    have /esym := edge_and_left_vertical_eq rltr (esym (etrans atl rr')).
    by move/andP: rone => [] -> _ /eqP.
  by move/eqP/psue_left_edge: atl; rewrite subr_gt0 -req.
have rue' : (r <<< e) = (pue_formula r (left_pt e) r' < 0).
  move: rone=> /andP[] /[dup] tmp/pue_formula_triangle_on_edge + _ => /(_ r).
(* TODO : fix pue_formula_triangle_on_edge for cycle *)
  rewrite (pue_formula_opposite (left_pt _)).
  rewrite (pue_formula_opposite (left_pt _) _ (right_pt _)) !mulrN.
  rewrite inj_eq; last by apply: oppr_inj.
  move/eqP => signcond.
  move: (edge_cond e); rewrite -subr_gt0 => /pmulr_rlt0 <-.
  by rewrite signcond pmulr_rlt0; last rewrite subr_gt0 -rr'.
have inr' : p_x (left_pt e) < p_x r' by rewrite -rr'.
have /psue_right_edge : p_x (right_pt (Bedge inr')) == p_x r.
  by rewrite /= rr' eqxx.
by rewrite rue' subr_lt0.
Qed.

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

Lemma under_edge_strict_lower_y r r' e :
  p_x r = p_x r' -> r != r' -> r <<= e -> r' === e -> p_y r < p_y r'.
Proof.
move=> xs nq under on'.
have  vr : valid_edge e r by move: on'; rewrite /valid_edge xs=> /andP[].
move: under; rewrite (under_onVstrict vr)=> /orP[on | ].
  by case/negP: nq; rewrite pt_eqE (on_edge_same_point on on') xs eqxx.
by rewrite (strict_under_edge_lower_y xs).
Qed.

Lemma above_edge_strict_higher_y r r' e :
  p_x r = p_x r' -> r != r' -> r >>= e -> r' === e -> p_y r' < p_y r.
Proof.
move=> xs nq above on'.
have  vr : valid_edge e r by move: on'; rewrite /valid_edge xs=> /andP[].
move: above; rewrite (strict_under_edge_lower_y xs on') // -leNgt le_eqVlt.
move/orP=> [/eqP ys | //].
by case/negP: nq; rewrite pt_eqE xs ys !eqxx.
Qed.

Lemma under_edge_lower_y r r' e :
  p_x r = p_x r' -> r' === e -> (r <<= e) = (p_y r <= p_y r').
Proof.
move=> rr' rone.
have valre : valid_edge e r by case/andP: rone; rewrite /valid_edge rr'.
move: (valre)=> /andP[] + _; rewrite le_eqVlt=> /orP[/eqP atl| inr].
  have req : r' = left_pt e.
    have rltr : p_x r' < p_x (right_pt e) by rewrite -rr' -atl edge_cond.
    have /esym := edge_and_left_vertical_eq rltr (esym (etrans atl rr')).
    by move/andP: rone => [] -> _ /eqP.
  by move/eqP/pue_left_edge: atl; rewrite subr_ge0 -req.
have rue' : (r <<= e) = (pue_formula r (left_pt e) r' <= 0).
  move: rone=> /andP[] /[dup] tmp/pue_formula_triangle_on_edge + _ => /(_ r).
(* TODO : fix pue_formula_triangle_on_edge for cycle *)
  rewrite (pue_formula_opposite (left_pt _)).
  rewrite (pue_formula_opposite (left_pt _) _ (right_pt _)) !mulrN.
  rewrite inj_eq; last by apply: oppr_inj.
  move/eqP => signcond.
  move: (edge_cond e); rewrite -subr_gt0 => /pmulr_rle0 <-.
  by rewrite signcond pmulr_rle0; last rewrite subr_gt0 -rr'.
have inr' : p_x (left_pt e) < p_x r' by rewrite -rr'.
have /pue_right_edge : p_x (right_pt (Bedge inr')) == p_x r.
  by rewrite /= rr' eqxx.
by rewrite rue' subr_le0.
Qed.

Lemma aligned_trans a a' b p : p_x a != p_x b ->
  pue_formula a' a b == 0 ->
  pue_formula p a b == 0 -> pue_formula p a' b == 0.
Proof.
rewrite -pue_formula_cycle.
move=> bna /[dup]/pue_formula_triangle_on_edge proc a'ab pab.
have/mulfI/inj_eq <-  : p_x a - p_x b != 0 by rewrite subr_eq0.
rewrite -pue_formula_cycle -(eqP (proc _)).
by rewrite pue_formula_cycle (eqP pab) !mulr0.
Qed.

Lemma pue_formula_change_ext a b a' b' p :
  p_x a < p_x b -> p_x a' < p_x b' ->
  pue_formula a' a b == 0 -> pue_formula b' a b == 0 ->
  sg (pue_formula p a b) = sg (pue_formula p a' b').
Proof.
move=> altb altb' ona onb.
have/pue_formula_triangle_on_edge:= ona => /(_ p)/eqP ona'.
have/pue_formula_triangle_on_edge:= onb => /(_ p)/eqP onb0.
have/pue_formula_triangle_on_edge: pue_formula b' a' a == 0.
  have bna : p_x b != p_x a by case: ltrgtP altb.
  by rewrite (aligned_trans bna) //
       pue_formula_opposite oppr_eq0 pue_formula_cycle.
move=>/(_ p)/eqP onb'.
have difab : 0 < p_x b - p_x a by rewrite subr_gt0.
have difab' : 0 < p_x b' - p_x a' by rewrite subr_gt0.
have [ | | aa' ] := ltrgtP (p_x a) (p_x a'); last first.
- set w := Bedge altb.
  have/on_edge_same_point tmp : a === Bedge altb by exact: left_on_edge.
  have/(tmp _) : a' === Bedge altb.
    by rewrite /point_on_edge ona /valid_edge /= -aa' lexx ltW.
  rewrite aa'=> /(_ (eqxx _))/eqP ays.
  have aa : a = a' by move: (a) (a') aa' ays=> [? ?][? ?] /= -> ->.
  rewrite -aa pue_formula_opposite [in RHS]pue_formula_opposite.
  rewrite -[RHS]mul1r -(gtr0_sg difab) -sgrM mulrN onb0 [X in _ - X]aa' -mulrN.
  by rewrite sgrM (gtr0_sg difab') mul1r.
- rewrite -subr_gt0=> xalta'; rewrite -[RHS]mul1r -(gtr0_sg xalta') -sgrM.
  rewrite [in RHS]pue_formula_opposite mulrN onb' -mulrN sgrM (gtr0_sg difab').
  rewrite -pue_formula_opposite -[in RHS]pue_formula_cycle.
  rewrite -(gtr0_sg difab) -sgrM ona' [in RHS]pue_formula_opposite.
  by rewrite mulrN -mulNr opprB sgrM (gtr0_sg xalta') mul1r.
rewrite -subr_lt0=> xa'lta; apply/esym. 
rewrite pue_formula_opposite -[X in -X]mul1r -mulNr sgrM sgrN1.
rewrite -(ltr0_sg xa'lta) -sgrM onb' sgrM (gtr0_sg difab').
rewrite pue_formula_opposite -pue_formula_cycle sgrN mulrN -(gtr0_sg difab).
rewrite -sgrM ona' -sgrN -mulNr opprB sgrM (ltr0_sg xa'lta).
by rewrite pue_formula_opposite sgrN mulrN mulNr opprK mul1r.
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

have ydiff : p_y p <= p_y p'.
  by rewrite -(under_edge_lower_y eqx' poep').

rewrite eqx' in eqx''.
have puep' := (point_on_edge_under  poep' pulh purh).
have y'diff : p_y p' <= p_y p''.
  by rewrite -(under_edge_lower_y eqx'' poep'').
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

have ydiff : p_y p < p_y p'.
  by rewrite -(strict_under_edge_lower_y eqx' poep').

rewrite eqx' in eqx''.
have puep' := (point_on_edge_under  poep' pulh purh).
have y'diff : p_y p' <= p_y p''.
  by rewrite -(under_edge_lower_y eqx'' poep'').
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

have ydiff : p_y p <= p_y p'.
  by rewrite -(under_edge_lower_y eqx' poep').
rewrite eqx' in eqx''.
symmetry in eqx''.
have pabp' := (point_on_edge_above  poep'' pabhl pabhr).
have y'diff : p_y p' <= p_y p''.
  by rewrite leNgt -(strict_under_edge_lower_y eqx'' poep').
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

have ydiff : p_y p < p_y p'.
  by rewrite -(strict_under_edge_lower_y eqx' poep').

rewrite eqx' in eqx''.
symmetry in eqx''.
have pabp' := (point_on_edge_above  poep'' pabhl pabhr).
have y'diff : p_y p' <= p_y p''
   by rewrite leNgt -(strict_under_edge_lower_y eqx'' poep').
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

Definition open_limit c :=
  min (p_x (right_pt (low c))) (p_x (right_pt (high c))).

Definition left_limit (c : cell) :=
  p_x (last dummy_pt (left_pts c)).

Definition right_limit c := p_x (last dummy_pt (right_pts c)).

Definition inside_open_cell p c :=
  [&& contains_point p c & left_limit c <= p_x p <= open_limit c].

Definition inside_closed_cell p c :=
  contains_point p c && (left_limit c <= p_x p <= right_limit c).

Lemma edge_dir_intersect p1 p2 e1 :
  p_x p1 != p_x p2 ->
  ~~(p1 <<= e1) -> p2 <<< e1 ->
 exists p, pue_formula p (left_pt e1) (right_pt e1) = 0 /\
      pue_formula p p1 p2 = 0 /\
   (forall q, pue_formula q (left_pt e1) (right_pt e1) = 0 ->
       pue_formula q p1 p2 = 0 -> p = q).
Proof.
move=> dif12.
rewrite /point_under_edge pue_formulaE -ltNge => ca.
rewrite /point_strictly_under_edge pue_formulaE => cu.
have [px [py []]] := line_intersection dif12 ca cu.
rewrite -/(p_y (Bpt px py)); set py' := (p_y (Bpt px py)).
rewrite -/(p_x (Bpt px py)) /py' {py'}.
move: ca cu; rewrite -4!pue_formulaE=> ca cu on_line1 [] on_line2 uniq.
exists (Bpt px py); rewrite on_line1 on_line2;split;[ | split]=> //.
by move=> [qx qy]; rewrite !pue_formulaE=> /uniq => U; move=> {}/U[] /= -> ->.
Qed.

Lemma intersection_middle_au e1 e2 :
  ~~ (left_pt e2 <<= e1) -> right_pt e2 <<< e1 ->
  exists p, pue_formula p (left_pt e1) (right_pt e1) = 0 /\ p === e2.
Proof.
move=> /[dup] ca; rewrite -ltNge=> ca' cu.
have le2xnre2x : p_x (left_pt e2) != p_x (right_pt e2).
  by have := edge_cond e2; rewrite lt_neqAle=> /andP[].
have [p [p1 [p2 pu]]] := edge_dir_intersect le2xnre2x ca cu.
exists p; rewrite p1; split=> //.
rewrite /point_on_edge p2 eqxx /= /valid_edge.
have/eqP ol2 := p2.
have := pue_formula_on_edge (left_pt e1) (right_pt e1) ol2 => /=.
rewrite p1 mulr0 eq_sym addrC addr_eq0 -mulNr opprB=> /eqP signcond.
case : (ltP (p_x p) (p_x (right_pt e2))).
  move=>/[dup]/ltW ->; rewrite andbT -subr_gt0 -subr_le0.
  rewrite -(pmulr_lgt0 _ ca') signcond.
  by rewrite nmulr_lgt0 // => /ltW.
move=>/[dup] re2lp.
rewrite -subr_le0 -(pmulr_lle0 _ ca') signcond.
by rewrite nmulr_lle0 // subr_ge0=> /(le_trans re2lp); rewrite leNgt edge_cond.
Qed.

Lemma intersection_middle_ua e1 e2 :
  left_pt e2 <<< e1 -> ~~(right_pt e2 <<= e1) ->
  exists p, pue_formula p (left_pt e1) (right_pt e1) = 0 /\ p === e2.
Proof.
move=> cu /[dup] ca; rewrite -ltNge=> ca'.
have re2xnle2x : p_x (right_pt e2) != p_x (left_pt e2).
  by have := edge_cond e2; rewrite lt_neqAle eq_sym=> /andP[].
have [p [p1 [p2 pu]]] := edge_dir_intersect re2xnle2x ca cu.
move: p2; rewrite pue_formula_opposite pue_formula_cycle => /eqP.
rewrite oppr_eq0=> /[dup] ol2 /eqP p2.
exists p; rewrite p1; split=> //.
rewrite /point_on_edge p2 eqxx /= /valid_edge.
have := pue_formula_on_edge (left_pt e1) (right_pt e1) ol2 => /=.
rewrite p1 mulr0 eq_sym addrC addr_eq0 -mulNr opprB=> /eqP signcond.
case : (ltP (p_x p) (p_x (right_pt e2))).
  move=>/[dup]/ltW ->; rewrite andbT -subr_gt0 -subr_le0.
  rewrite -(nmulr_llt0 _ cu) signcond.
  by rewrite pmulr_llt0 // => /ltW.
move=>/[dup] re2lp.
rewrite -subr_le0 -(nmulr_lge0 _ cu) signcond.
by rewrite pmulr_lge0 // subr_ge0=> /(le_trans re2lp); rewrite leNgt edge_cond.
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

Definition inspect [A : Type](a : A) : {x : A | a = x}.
exists a; apply: erefl.  
Defined.

Fixpoint sum (n : nat) := match n with O => O | S p => (p + sum p)%N end.
Check forall (P : nat -> nat -> Prop),
  (P O O) -> (forall p, P p (sum p) -> P (S p) (p + sum p)%N) ->
  forall n, P n (sum n).

Fixpoint f_ind (P : nat -> nat -> Prop) 
  (V1 : P O O) (V2 : forall p, P p (sum p) -> P (S p) (p + sum p)%N)
  (n : nat) : P n (sum n) :=
  match n return P n (sum n) with
  | O => V1
  | S p => V2 p (f_ind V1 V2 p)
  end.

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

Lemma lexPtEv_trans : transitive lexPtEv.
Proof. by move=> e2 e1 e3; rewrite /lexPtEv; apply: lexPt_trans. Qed.

Lemma lexPtEvcons ev a future : sorted  lexPtEv (ev::a::future) ->
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
    by move=> bt /inside_box_valid_bottom_top/(_ bt).
  rewrite has_seq1 /event_close_edge => edincEv insbox.
  rewrite /valid_edge /andP ltW.
    rewrite andTb.
    have h2 : right_pt ed = point ev.
      by apply /eqP.
    by rewrite h2.
  by [].
move => sorevBf.
have sorevF : sorted lexPtEv (ev :: future).
  by apply (lexPtEvcons sorevBf ).
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

Lemma adjacent_cells_sorted s :
  adjacent_cells s = sorted (fun c1 c2 => high c1 == low c2) s.
Proof.
case: s => [// | a s] /=.
elim: s a => [// | b s Ih] a /=.
by rewrite Ih.
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
  have fact1 : (0 < p_x p - p_x (left_pt e2)) by rewrite subr_gt0 -px.
  rewrite -(pmulr_rgt0 _ fact1) pue_formula_opposite mulrN.
  rewrite -(eqP (pue_formula_triangle_on_edge (left_pt e1) pone2')) -mulrN.
  rewrite -pue_formula_opposite pue_formula_cycle pmulr_rgt0 //.
  by apply: edge_and_right_vertical; rewrite -px.
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
  rewrite -(pmulr_rgt0 _ ce2).
  rewrite (eqP (pue_formula_on_edge (left_pt e1) (right_pt e1) pone2')).
  rewrite ltNge arith //.
    apply: mulr_ge0_le0; first by rewrite -px subr_ge0.
    by move: re2b; rewrite /point_under_edge -pue_formula_cycle.
  apply: mulr_ge0_le0; first by rewrite -px subr_ge0.
  by move: le2b; rewrite /point_under_edge -pue_formula_cycle.
suff case2 : ~~(left_pt e1 <<= e2) -> e2 <| e1 by [].
move=> above; case: (nc) => // /orP[]; first by rewrite (negbTE above).
rewrite /point_strictly_under_edge -!leNgt => /andP[] le2a re2a.
have pyne1 : p_y (left_pt e1) != p_y p by apply: dify; right.
have ys : p_y p < p_y (left_pt e1).
  by rewrite -main;move: (above); rewrite /point_under_edge -ltNge.
have : 0 < pue_formula (left_pt e1) p (right_pt e1).
  by rewrite edge_and_left_vertical // (edge_cond e1).
rewrite pue_formula_opposite -pue_formula_cycle.
rewrite -(pmulr_rgt0 _ dife2) mulrN.
move: (eqP (pue_formula_on_edge (left_pt e1) (right_pt e1) pone2')) => ->.
by rewrite oppr_gt0 ltNge addr_ge0 // mulr_ge0 // -px subr_ge0.
Qed.

Lemma opening_cells_seq_edge_shift p oe le he :
  {in oe, forall g, left_pt g == p} ->
  valid_edge le p -> valid_edge he p ->
  le :: [seq high i | i <- opening_cells p oe le he] =
  rcons [seq low i | i <- opening_cells p oe le he] he.
Proof.
move=> + + vh.
elim: oe le => [ | g oe Ih] le leftg vl.
  rewrite /=; case: (exists_point_valid vl) => [p1 ->].
  by case: (exists_point_valid vh) => [p2 ->].
rewrite /=; case: (exists_point_valid vl) => [p1 ->] /=.
rewrite Ih //; last first.
  have gin : g \in g :: oe by rewrite inE eqxx.
  have := @valid_edge_extremities g p; rewrite (eqP (leftg g gin)) eqxx.
  by apply.
by move=> g' gin; apply: leftg; rewrite inE gin orbT.
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

Lemma opening_cells_right_form' (ctxt s : seq edge) p low_e high_e :
p >>= low_e -> p <<< high_e -> valid_edge high_e p ->
low_e \in ctxt -> high_e \in ctxt ->
low_e <| high_e -> {in s, forall g, left_pt g == p} ->
{in ctxt &, no_crossing} ->
{subset s <= ctxt} ->
path edge_below low_e s ->
forall new_open_cells,
opening_cells p s low_e high_e = new_open_cells ->
s_right_form new_open_cells.
Proof.
move=> + ph vh + hin + + noc + +.
elim: s low_e => [ | g1 edges IH] low_e
  pabove lin lowhigh outs allin sorted_e /=.
  case v_i_l_eq :
   (vertical_intersection_point p low_e)=> [a1 | ]; last by move=> s <-.
  case v_i_h_eq :
   (vertical_intersection_point p high_e) => [a2 | ]; last by move=> s <-.
  by case: ifP => [a2e | a2ne];
    case: ifP => [a1e | a1ne] s <-; rewrite /=/right_form /= ?andbT.
case v_i_l_eq :
   (vertical_intersection_point _ low_e)=> [a1 | ]; last by move=> s <-.
have outs' : {in edges, forall g, left_pt g == p}.
  by move=> g gin; apply outs; rewrite inE gin orbT.
have allin' : {subset edges <= ctxt}.
  by move=> g gin; rewrite allin // inE gin orbT.
have sorted_e' : path edge_below g1 edges by apply: (path_sorted sorted_e).
have /eqP gl : left_pt g1 == p by rewrite outs // inE eqxx.
have g1belowhigh : g1 <| high_e.
  have gin' : g1 \in ctxt by rewrite allin // inE eqxx.
  have/no_crossingE := noc g1 high_e gin' hin.
  by rewrite gl=>/(_ vh)=> -[]/(_ ph).
have pong : p === g1 by rewrite -gl left_on_edge.
have paboveg1 : p >>= g1 by rewrite strict_nonAunder ?pong //; case/andP: pong.
move: (sorted_e) => /=/andP[] low_eg1 _.
have g1in : g1 \in ctxt by rewrite allin // inE eqxx.
by case: ifP => _ s <- /=; rewrite /right_form /= ?low_eg1 /=; apply: (IH g1).
Qed.

Lemma opening_cells_right_form e low_e high_e :
valid_edge high_e (point e) ->
point e >>= low_e -> point e <<< high_e ->
low_e <| high_e ->
{in outgoing e, forall g, left_pt g == point e} ->
{in outgoing e, forall g, low_e <| g} ->
{in outgoing e, forall g, g <| high_e} ->
{in outgoing e &, no_crossing} ->
forall new_open_cells,
opening_cells (point e) 
  (sort edge_below (outgoing e)) low_e high_e = new_open_cells ->
s_right_form new_open_cells.
(*  && (head low_e [seq low c | c <- new_open_cells] == low_e). *)
Proof.
set mainsort := fun l => (perm_mem (permEl (perm_sort edge_below l))).
move=> vh pabove punder lowhigh outs alla allb noc new oe; apply/allP.
have noc' : {in low_e :: high_e :: outgoing e &, no_crossing}.
  move=> e1 e2; rewrite !inE !orbA =>/orP[e1lh |e1in ]/orP[e2lh |e2in].
    by apply/orP;move:e1lh e2lh=> /orP[]/eqP -> /orP[]/eqP ->;
      rewrite ?edge_below_refl ?lowhigh ?orbT.
    - by move: e1lh=> /orP[]/eqP ->;apply/orP;
         rewrite/below_alt ?alla ?allb ?orbT.
    - by move: e2lh=> /orP[]/eqP ->; apply/orP;
         rewrite/below_alt ?alla ?allb ?orbT.
    by apply: noc.
have sorted_e : sorted edge_below (sort edge_below (outgoing e)).
  have /sort_sorted_in : {in low_e :: outgoing e &, total edge_below}.
    move=> e1 e2; rewrite !inE =>/orP[/eqP -> |e1in ]/orP[/eqP -> |e2in].
    - apply/orP; left; apply/orP; left; rewrite /point_under_edge.
      by rewrite (eqP (proj1 (pue_formula_two_points _ _)))
              (eqP (proj1 (proj2 (pue_formula_two_points _ _)))).
    - by rewrite alla.
    - by rewrite alla ?orbT.
    - by apply/orP/noc.
  by apply; apply/allP=> x xin /=; apply/orP; right; exact: xin.
have /sub_in1/= trsf : {subset sort edge_below (outgoing e) <= outgoing e}.
  by move=> x; rewrite mainsort.
move/trsf:outs => {}outs.
have [lin hin] : (low_e \in [:: low_e, high_e & outgoing e]) /\
   (high_e \in [:: low_e, high_e & outgoing e]).
  by split; rewrite !inE eqxx ?orbT.
have slho : {subset (sort edge_below (outgoing e)) <=
               [:: low_e, high_e & outgoing e]}.
  by move=> x; rewrite mainsort => xin; rewrite !inE xin ?orbT.
move=> x xin.
have srt : sorted edge_below (low_e :: sort edge_below (outgoing e)).
  case sq : (sort edge_below (outgoing e)) => [// | a tl].
    rewrite -[sorted _ _]/((low_e <| a) && sorted edge_below (a :: tl)).
    by rewrite -sq sorted_e andbT alla // -mainsort sq inE eqxx.
have := (opening_cells_right_form' pabove punder vh lin hin lowhigh outs noc' slho srt oe).
by move=>/allP; apply.
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
  {in outgoing ev, forall e, left_pt e == point(ev)}.

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

Lemma adjacent_catW s1 s2 : 
  adjacent_cells (s1 ++ s2) -> adjacent_cells s1 /\ adjacent_cells s2.
Proof.
case : s1 => [ // | c s1 /=].
rewrite adj_aux_path cat_path => /andP[].
rewrite -2!adj_aux_path => leftside /adjacent_cons rightside.
split;[exact leftside | exact rightside].
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

Lemma adjacent_opening_aux' p s le he new :
  opening_cells p s le he = new -> adjacent_cells_aux new le.
Proof.
elim: s le new => [ | g s Ih] le new /=; set vip := vertical_intersection_point.
  case vip1 : (vip p le) => [p1 | ]; last by move=> <-.
  case vip2 : (vip p he) => [p2 | ]; last by move=> <-.
  by case: ifP => _ <- /=; rewrite eqxx.
case: (vip p le) => [p1 | ]; last by move=> <-.
by case: ifP => testres <- /=; rewrite eqxx /=; apply: Ih.
Qed.

Lemma adjacent_opening' p s le he:
  adjacent_cells (opening_cells p s le he).
Proof.
case: s => [| g s ] /=; set vip := vertical_intersection_point.
  case vip1 : (vip p le) => [p1 | ]; last by [].
  by case vip2 : (vip p he) => [p2 | ].
case: (vip p le) => [p1 | ]; last by [].
by apply: (adjacent_opening_aux' erefl).
Qed.
  
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
by rewrite -(under_edge_lower_y px_eq poeh).
Qed.

Definition no_crossing'  : Prop:=
 forall e e',
 valid_edge e (left_pt e') ->
(left_pt e' <<< e  -> e' <| e)  /\
(~ (left_pt e' <<= e)  -> e <| e').

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
have [/eqP | {}nc ] := nc _ _ e1in e2in; first by rewrite (negbTE e1ne2).
have [/eqP | {}nc' ] := nc' _ _ e1in e2in; first by rewrite (negbTE e1ne2).
have [ | ] := boolP(e1 <| e2); first by left.
have [ | ] := boolP(e2 <| e1); first by right.
rewrite /edge_below; rewrite !negb_or !negb_and !negbK=> noc.
suff [it | [p [pone1 pone2]]] :
  below_alt e1 e2 \/ exists p, p === e1 /\ p === e2; first by [].
  have : p \in [:: left_pt e1; right_pt e1] by apply: nc.
  rewrite !inE=> pext.
  set other := if p == left_pt e1 then right_pt e1 else left_pt e1.
  have dif : right_pt e1 != left_pt e1.
    apply/eqP=> abs.
    move: (edge_cond e1); rewrite lt_neqAle eq_sym => /andP[].
    by rewrite abs eqxx.
  have [ u' | /underWC a'] := boolP (other <<= e2).
    left; apply/orP; left.
    move: (pone2) u'=> /andP[] _ /under_onVstrict.
    rewrite pone2 /= /other.
    by  move: pext=> /orP[] /eqP -> ->; rewrite ?eqxx ?(negbTE dif) ?andbT.
  right; apply/orP; right.
    move: (pone2) a'=> /andP[] _/strict_nonAunder; rewrite pone2 /= /other.
    by move: pext=>/orP[]/eqP -> ->; rewrite ?eqxx ?(negbTE dif)=> ->.
move: noc {nc nc'} => /andP[] /orP[le2a | re2a].
  have [ re2u | re2a _] := boolP(right_pt e2 <<< e1); last first.
    by left; left; apply/orP; right; rewrite re2a underWC.
  have dif2 : p_x (left_pt e2) != p_x (right_pt e2).
    by have := edge_cond e2; rewrite lt_neqAle => /andP[].
  have [r [_ [ _ uniq]]] := edge_dir_intersect dif2 le2a re2u.
  move=> /orP[le1u | re1u].
    have [re1u | re1a] := boolP(right_pt e1 <<= e2).
      by left; left; apply/orP; left; rewrite re1u underW.
    have [p [pe2 pe1]] := intersection_middle_ua le1u re1a.
    have [q [qe1 qe2]] := intersection_middle_au le2a re2u.
    move: (pe1) (qe2)=> /andP[] /eqP pe1' _ /andP[] /eqP qe2' _.
    have rq := uniq _ qe1 qe2'; have rp := uniq _ pe1' pe2.
    by right; exists r; rewrite [X in X === e2]rq rp.
  have [le1u | le1a] := boolP(left_pt e1 <<= e2).
      by left; left; apply/orP; left; rewrite le1u underW.
  have [q [qe1 qe2]] := intersection_middle_au le2a re2u.
  have [p [pe2 pe1]] := intersection_middle_au le1a re1u.
  move: (pe1) (qe2)=> /andP[] /eqP pe1' _ /andP[] /eqP qe2' _.
  have rq := uniq _ qe1 qe2'; have rp := uniq _ pe1' pe2.
  by right; exists r; rewrite [X in X === e2]rq rp.
have [ le2u | le2a _] := boolP(left_pt e2 <<< e1); last first.
    by left; left; apply/orP; right; rewrite le2a underWC.
have dif2 : p_x (right_pt e2) != p_x (left_pt e2).
  by have := edge_cond e2; rewrite lt_neqAle eq_sym => /andP[].
have [r [_ [ _ uniq]]] := edge_dir_intersect dif2 re2a le2u.
have transfer a b c : pue_formula a b c = 0 -> pue_formula a c b = 0.
  by move=> abc; rewrite pue_formula_opposite pue_formula_cycle abc oppr0.
move=> /orP[le1u | re1u].
  have [re1u | re1a] := boolP(right_pt e1 <<= e2).
    by left; left; apply/orP; left; rewrite re1u underW.
  have [p [/transfer pe2 pe1]] := intersection_middle_ua le1u re1a.
  have [q [qe1 qe2]] := intersection_middle_ua le2u re2a.
  move: (pe1) (qe2)=> /andP[] /eqP pe1' _ /andP[] /eqP /transfer qe2' _.
  have rq := uniq _ qe1 qe2'; have rp := uniq _ pe1' pe2.
  by right; exists r; rewrite [X in X === e2]rq rp.
have [le1u | le1a] := boolP(left_pt e1 <<= e2).
  by left; left; apply/orP; left; rewrite le1u underW.
have [q [qe1 qe2]] := intersection_middle_ua le2u re2a.
have [p [/transfer pe2 pe1]] := intersection_middle_au le1a re1u.
move: (pe1) (qe2)=> /andP[] /eqP pe1' _ /andP[] /eqP /transfer qe2' _.
have rq := uniq _ qe1 qe2'; have rp := uniq _ pe1' pe2.
by right; exists r; rewrite [X in X === e2]rq rp.
Qed.

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
  have : p_y low_p <= p_y (point e).
    by rewrite leNgt -(strict_under_edge_lower_y lx_eq poel).
  rewrite /lexePt lx_eq eqxx=> ->.
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

Definition events_to_edges := flatten \o (map outgoing).

Definition cell_edges cells := map low cells ++ map high cells.
Definition all_edges cells events :=
  cell_edges cells ++ events_to_edges events.

Lemma step_keeps_left_pts_inf e (future_events : seq event) p old_open : 
inside_box (point e) -> out_left_event e ->
s_right_form old_open -> seq_valid old_open (point e) ->
adjacent_cells old_open -> cells_bottom_top old_open ->
close_alive_edges old_open (e :: future_events) ->
close_edges_from_events (e :: future_events) ->
{in  all_edges old_open (e :: future_events) &, no_crossing} ->
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
    by move: n_c; rewrite /all_edges /cell_edges=> /(sub_in2 (sub_cat _ _)).
  by apply: open_cells_decomposition_low_under_high _ _ _ _ _ op_c_d.
have n_c' : {in rcons (low_e :: sort edge_below (outgoing e)) high_e &, no_crossing}.
  have [lc1 [lc2 [lc1in [lc2in]]]] := l_h_in_open cbtom adjopen insboxe.
    rewrite op_c_d /= => [][lowlc1 highlc2].
  have subseq:
    forall x, x \in rcons (low_e :: sort edge_below (outgoing e)) high_e ->
          x \in all_edges old_open (e :: future_events).
    move=> x; rewrite -cats1 mem_cat 2!inE 2!mem_cat orbAC=> /orP[].
      by move=>/orP[]/eqP ->; rewrite -?lowlc1 -?highlc2 map_f ?orbT.
    rewrite mem_sort=> xin; apply/orP; right.
    by apply/flattenP; exists (outgoing e); rewrite // inE eqxx.
  by apply: (sub_in2 subseq).
have lowinfe' : ~~ (point e <<< low_e).
  move : lowinfe => lowinfe.
  apply (underWC lowinfe).
have cinfe := (opening_cells_left outlefte lowinfe' einfhigh vallow valhigh n_c' linfh cin).
by apply/(le_trans (lexePt_xW cinfe))/lexePt_xW/lexPtW.
Qed.

Lemma outgoing_conditions (s oe : seq edge) p he le :
  p >>> le -> p <<< he -> le \in s -> he \in s ->
  valid_edge le p -> valid_edge he p ->
  {subset oe <= s} ->
  {in s &, no_crossing} ->
  {in oe, forall g, left_pt g == p} ->
  [/\ {in oe, forall g, le <| g}, {in oe, forall g, g <| he} &
      {in oe &, no_crossing}].
Proof.
move=> pl ph lein hein vl vh oesub noc lefts; split.
+ move=> g gin; have := noc _ _ (oesub _ gin) lein.
  move=>/no_crossingE[]; first by rewrite (eqP (lefts _ _)) // sval.
  by rewrite (eqP (lefts _ _)) // => _ /(_ pl).
+ move=> g gin; have := noc _ _ (oesub _ gin) hein.
  move=>/no_crossingE[]; first by rewrite (eqP (lefts _ _)) // sval.
  by rewrite (eqP (lefts _ _)) // => /(_ ph).
exact: (sub_in2 oesub).
Qed.

Lemma step_keeps_right_form e open closed op2 cl2 :
  cells_bottom_top open -> adjacent_cells open -> 
  inside_box (point e) -> seq_valid open (point e) ->
  {in ([seq low c | c <- open] ++ [seq high c | c <- open]) ++
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
have/andP[lP hP] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have [c1 [c2 [c1in [c2in]]]] := l_h_in_open cbtom adj inbox_e.
rewrite oe /= => [][le_eq he_eq].
set bigs := cell_edges open ++ outgoing e.
have lein : le \in bigs by rewrite !mem_cat -le_eq map_f ?orbT.
have hein : he \in bigs by rewrite !mem_cat -he_eq map_f ?orbT.
have obig : {subset (outgoing e) <= bigs}.
  by move=> g gin; rewrite !mem_cat gin ?orbT.
have lev : valid_edge le (point e) by have [] := l_h_valid _ _ _ _ oe.
have hev : valid_edge he (point e) by have [] := l_h_valid _ _ _ _ oe.
have [edgesabove edgesbelow nocout] :=
   outgoing_conditions lP hP lein hein lev hev obig noc oute.
have /allP rfn : s_right_form 
    (opening_cells (point e) (sort edge_below (outgoing e)) le he).
  apply: (opening_cells_right_form hev (underWC lP) hP) => //.
  apply: (open_cells_decomposition_low_under_high _ _ _ _ _ _ oe)=> //.
  by move: noc; apply: sub_in2=> x xin; rewrite mem_cat xin.
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
  {subset cell_edges (opening_cells p s le he) <=
      s ++ [:: le; he]}.
Proof.
by move=> g; rewrite mem_cat=> /orP[] /mapP[c cin ->];
  have := opening_cells_subset cin => /andP[];
  rewrite /= !inE => /orP[/eqP lowin | oth] /orP[/eqP hiin | oth'];
  rewrite ?lowin ?hiin ?oth mem_cat ?inE ?eqxx ?oth ?oth' ?orbT.
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
   (opening_cells (point e) (sort edge_below (outgoing e)) le he) <=
      cell_edges open ++ outgoing e}.
  set srt := sort _ _.
  move=> g gin.
  have [c cin geq] :
   exists2 c, c \in opening_cells (point e) srt le he &
          (g == low c) || (g == high c).
    move: gin; rewrite mem_cat.
    by move=> /orP[]/mapP[c cin geq]; exists c => //; rewrite geq eqxx ?orbT.
  have := opening_cells_subset cin; rewrite 2!inE /srt !mem_sort mem_cat.
  have [loc [hic [locin [hicin]]]] := l_h_in_open cbtom adj inbox_e.
  rewrite oe /= => -[loeq hieq].
  have [lein hein] : le \in cell_edges open /\ he \in cell_edges open.
    by rewrite !mem_cat -loeq -hieq 2?map_f ?orbT.
  by move: geq=>/orP[] /eqP u > => /andP[] /orP[/eqP v | v ] /orP[/eqP w | w];
    rewrite ?u ?v ?w ?lein ?hein ?orbT.
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
    by rewrite adj_aux_path cat_path last_rcons /= => /andP[] _ /andP[].
  have ain : a \in cc by rewrite dec -cats1 !(mem_cat, inE) eqxx ?orbT.
  apply: (under_above_on vlc _ plc).
  by rewrite -ac; move: (allP ctps _ ain)=> /andP[].
case: s2 dec => [// | a s2] + _.
rewrite -[ c :: _]/([:: c] ++ _) catA => dec.
have /eqP ca : high c == low a.
  case: s1 dec adj => [ | b s1] -> /=; first by move=> /andP[] ->.
  by rewrite adj_aux_path cats1 cat_path last_rcons /= => /andP[] _/andP[].
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
  sorted lexPt [seq point x | x <- (e :: evs)] ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  out_left_event e ->
  s_right_form open ->
  close_alive_edges open (e :: evs) ->
  close_edges_from_events (e :: evs) ->
  {in cell_edges open ++ flatten [seq outgoing i | i <- e :: evs] &,
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
have inclosing : forall c, c \in cc -> inside_open_cell q c ->
  (forall c, c \in cc -> valid_edge (low c) (point e) &&
     (valid_edge (high c) (point e))) ->
  exists2 c', c' \in closing_cells (point e) cc & inside_closed_cell q c'.
  move=> c cin ins allval.
  have /allP ctps : forall c, c \in cc -> contains_point (point e) c.
    by move=> ?; apply: (open_cells_decomposition_contains oe).
  have [/eqP/esym lel [/eqP/esym heh _]] :=
     l_h_c_decomposition oe (exists_cell cbtom adj (inbox_e)).
  have/andP [eabovel ebelowh] :=
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


Lemma common_point_edges_y_left r r1 r2 e1 e2 :
   valid_edge e1 r -> p_x r <= p_x (left_pt e1) ->
     p_x r = p_x r1 -> p_x r = p_x r2 -> left_pt e1 === e2 ->
     r1 === e1 -> r2 === e2 ->
     p_y r1 = p_y r2.
Proof.
move=> v xl rr1 rr2 e1e2 re1 re2.
have xl': p_x r = p_x (left_pt e1) by apply: le_anti; rewrite xl; case/andP:v.
have:= on_edge_same_point e1e2 re2; rewrite -xl' rr2 eqxx=> /(_ isT)/eqP <-.
have:= on_edge_same_point (left_on_edge _) re1.
by rewrite -xl' rr1 eqxx=>/(_ isT)/eqP<-.
Qed.

Lemma common_point_edges_y_right r r1 r2 e1 e2 :
 valid_edge e1 r -> p_x (right_pt e1) <= p_x r ->
     p_x r = p_x r1 -> p_x r = p_x r2 -> right_pt e1 === e2 ->
     r1 === e1 -> r2 === e2 ->
     p_y r1 = p_y r2.
Proof.
move=> v xl rr1 rr2 e1e2 re1 re2.
have xl': p_x r = p_x (right_pt e1).
  by apply: le_anti; rewrite xl andbC; case/andP:v.
have:= on_edge_same_point e1e2 re2; rewrite -xl' rr2 eqxx=> /(_ isT)/eqP <-.
have:= on_edge_same_point (right_on_edge _) re1.
  by rewrite -xl' rr1 eqxx=>/(_ isT)/eqP<-.
Qed.

Lemma expand_valid p q (pq : p_x p < p_x q) e r :
  valid_edge (Bedge pq) r ->
  valid_edge e p -> valid_edge e q -> valid_edge e r.
Proof.
move=>/andP[]pr rq /andP[] lep pre /andP[]leq qre; rewrite /valid_edge.
by rewrite (le_trans lep) ?(le_trans rq).
Qed.

Lemma keep_under (p q : pt) e1 e2 :
  inter_at_ext e1 e2 ->
  {in [:: p; q] & [:: e1; e2], forall r e, valid_edge e r} ->
  p <<< e1 -> ~~ (p <<< e2) -> ~~(q <<< e1) -> ~~(q <<< e2).
Proof.
have left_ext r r1 r2 := @common_point_edges_y_left r r1 r2 e1 e2.
have right_ext r r1 r2 := @common_point_edges_y_right r r1 r2 e1 e2.
move=> noc val pue1 pae2 qae1; apply/negP=> que2; set v := valid_edge.
have : [/\ v e1 p, v e2 p, v e1 q & v e2 q].
  by split; apply: val; rewrite !inE eqxx ?orbT.
have pr e r: valid_edge e r ->
   exists r', [/\ valid_edge e r, r' === e & p_x r = p_x r'].
    move=>/[dup]vr/exists_point_valid[r' /intersection_on_edge [one xx]].
    by exists r'; constructor.
move=>[]/pr[p1 [vp1 pone1 p1p]] /pr[p2 [vp2 pone2 p2p]].
move=> /pr[q1 [vq1 qone1 q1q]] /pr[q2 [vq2 qone2 q2q]].
move: vp1 vp2 vq1 vq2 p1p p2p q1q q2q=>vp1 vp2 vq1 vq2 p1p p2p q1q q2q.
move: pone1 pone2 qone1 qone2=>pone1 pone2 qone1 qone2 {pr v val}.
set abbrev := strict_under_edge_lower_y.
have pylt : p_y p < p_y p1 by rewrite -(abbrev _ _ _ _ pone1).
have pyge : p_y p2 <= p_y p by rewrite leNgt -(abbrev _ _ _ _ pone2).
have qyge : p_y q1 <= p_y q by rewrite leNgt -(abbrev _ _ _ _ qone1).
have qylt : p_y q < p_y q2 by rewrite -(abbrev _ _ _ _ qone2).
have yp : p_y p2 < p_y p1 by rewrite (le_lt_trans pyge).
have yq : p_y q1 < p_y q2 by rewrite (le_lt_trans qyge).
move=> {pyge qyge pylt qylt abbrev}.
have [/[dup]p1p2 + /[dup] q1q2 +] : [/\ p_x p1 == p_x p2 & p_x q1 == p_x q2].
  by rewrite -p1p p2p -q1q q2q !eqxx.
move=>/eqP/esym/eqP p2p1 /eqP/esym/eqP q2q1.
move: (pone1) (pone2) (qone1) (qone2).
move=>/andP[]pl1 _ /andP[]pl2 _ /andP[]ql1 _ /andP[] ql2 _.
have [pltq | qltp | pq ] := ltrgtP (p_x p) (p_x q).
- have [p1q1 p2q2] : p_x p1 < p_x q1 /\ p_x p2 < p_x q2.
    by rewrite -p1p -q1q -p2p -q2q .
  set e3 := Bedge p1q1; set e4 := Bedge p2q2.
  have l3a : ~~(left_pt e3 <<= e4).
    by move/(@pue_left_edge e4):p2p1=> -> /=; rewrite subr_ge0 -ltNge.
  have r3u : right_pt e3 <<< e4.
    by move/(@psue_right_edge e4):q2q1=> -> /=; rewrite subr_lt0.
  have [pi [pi4 /andP[pi3 piint]]] := intersection_middle_au l3a r3u.
  have pi1 : pi === e1.
    apply/andP; split; last first.
      by apply: (expand_valid piint); rewrite /valid_edge -?p1p -?q1q.
    rewrite -sgr_eq0 (pue_formula_change_ext _ (edge_cond e1) p1q1) //.
    by rewrite (eqP pi3).
  have pi2 : pi === e2.
    apply/andP; split; last first.
      by apply:(expand_valid piint); rewrite /valid_edge -?p1p -?q1q.
    rewrite -sgr_eq0 (pue_formula_change_ext _ (edge_cond e2) p2q2) //.
    by rewrite pi4.
  move: piint; rewrite /valid_edge /e3/= -p1p -q1q=> /andP[] ppi piq.
  case: noc=> [E | /(_ pi pi1 pi2) piext]; first by move: pae2; rewrite -E pue1.
  move: (piext) ppi piq pi1 pi2 { pi3 pi4 }; rewrite !inE.
  move => /orP[]/eqP/[dup]pival -> ppi piq pi1 pi2.
    have abs := left_ext _ _ _ vp1 ppi p1p p2p pi2 pone1 pone2.
    by move: yp; rewrite abs ltxx.
  have abs := right_ext _ _ _ vq1 piq q1q q2q pi2 qone1 qone2.
  by move: yq; rewrite abs ltxx.
- have [q1p1 q2p2] : p_x q1 < p_x p1 /\ p_x q2 < p_x p2.
    by rewrite -p1p -q1q -p2p -q2q .
  set e3 := Bedge q1p1; set e4 := Bedge q2p2.
  have l3u : left_pt e3 <<< e4.
    by move/(@psue_left_edge e4):q2q1=> -> /=; rewrite subr_gt0.
  have r3a : right_pt e3 >>> e4.
    by move/(@pue_right_edge e4):p2p1=> -> /=; rewrite subr_le0 -ltNge.
  have [pi [pi4 /andP[pi3 piint]]] := intersection_middle_ua l3u r3a.
  have pi1 : pi === e1.
    apply/andP; split; last first.
      by apply: (expand_valid piint); rewrite /valid_edge -?p1p -?q1q.
    rewrite -sgr_eq0 (pue_formula_change_ext _ (edge_cond e1) q1p1) //.
    by rewrite (eqP pi3).
  have pi2 : pi === e2.
    apply/andP; split; last first.
      by apply:(expand_valid piint); rewrite /valid_edge -?p1p -?q1q.
    rewrite -sgr_eq0 (pue_formula_change_ext _ (edge_cond e2) q2p2) //.
    by rewrite pi4.
  move: piint; rewrite /valid_edge /e3/= -p1p -q1q=> /andP[] qpi pip.
  case: noc=> [E | /(_ pi pi1 pi2) piext]; first by move: pae2; rewrite -E pue1.
  move: (piext) qpi pip pi1 pi2 { pi3 pi4 }; rewrite !inE.
  move => /orP[]/eqP/[dup]pival -> qpi pip pi1 pi2.
    have abs := left_ext _ _ _ vq1 qpi q1q q2q pi2 qone1 qone2.
    by move: yq; rewrite abs ltxx.
  have abs := right_ext _ _ _ vp1 pip p1p p2p pi2 pone1 pone2.
  by move: yp; rewrite abs ltxx.
have := conj (on_edge_same_point pone1 qone1) (on_edge_same_point pone2 qone2).
rewrite -p1p -p2p pq q1q q1q2 !eqxx=> -[]/(_ isT)/eqP p1q1 /(_ isT)/eqP p2q2.
by move: yp; rewrite p1q1 p2q2; rewrite ltNge le_eqVlt yq orbT.
Qed.

Definition pvert_y (p : pt) (e : edge) :=
  match vertical_intersection_point p e with
    Some p' => p_y p'
  | None => 0
  end.

Lemma pvertE p e : valid_edge e p ->
  vertical_intersection_point p e = Some (Bpt (p_x p) (pvert_y p e)).
Proof.
move=> vep; rewrite /pvert_y.
have [p' p'P] := exists_point_valid vep; rewrite p'P.
have [one pxq] := intersection_on_edge p'P.
by rewrite pxq; case: (p') one.
Qed.

Lemma pvert_on p e : valid_edge e p ->
  Bpt (p_x p) (pvert_y p e) === e.
Proof.
move=> vep; rewrite /pvert_y.
have [p' p'P] := exists_point_valid vep; rewrite p'P.
have [one pxq] := intersection_on_edge p'P.
by rewrite pxq; case: (p') one.
Qed.

Definition on_pvert p e : p === e -> pvert_y p e = p_y p.
Proof.
move=> /[dup]/andP[] _ vpe pone.
by have := on_edge_same_point pone (pvert_on vpe) (eqxx _) => /eqP ->.
Qed.

Definition cmp_slopes e1 e2 :=
  sg((p_y (right_pt e2) - p_y (left_pt e2)) * 
     (p_x (right_pt e1) -p_x (left_pt e1)) - 
     (p_y (right_pt e1) - p_y (left_pt e1)) * 
     (p_x (right_pt e2) - p_x (left_pt e2))).

Definition pedge_below p e1 e2 := 
  (pvert_y p e1 < pvert_y p e2) || 
  ((pvert_y p e1 == pvert_y p e2) && (0 <= cmp_slopes e1 e2)).

Definition pedge_below' p e1 e2 := 
  (pvert_y p e1 < pvert_y p e2) || 
  ((pvert_y p e1 == pvert_y p e2) && (cmp_slopes e1 e2 <= 0)).

Lemma same_left_edge_below_slopes e1 e2 :
  left_pt e1 = left_pt e2 ->
  e1 <| e2 = (0 <= cmp_slopes e1 e2).
Proof.
move=> sameleft.
rewrite /edge_below/point_under_edge [in X in X || _]sameleft.
rewrite (eqP (proj1 (pue_formula_two_points _ _))) lexx /=.
rewrite /point_strictly_under_edge -[in X in _ || X]sameleft -!leNgt.
rewrite (eqP (proj1 (pue_formula_two_points _ _))) lexx /=.
rewrite !pue_formulaE !(proj1 (pue_f_eq_slopes _ _ _ _ _ _)).
rewrite  /cmp_slopes sameleft -opprB oppr_le0.
rewrite [X in (_ <= X - _) || _]mulrC.
rewrite [X in _ || (_ <= _ - X)]mulrC.
rewrite orbb.
by rewrite sgr_ge0.
Qed.

Lemma same_right_edge_below_slopes e1 e2 :
  right_pt e1 = right_pt e2 ->
  e1 <| e2 = (cmp_slopes e1 e2 <= 0).
Proof.
move=> sameright.
rewrite /edge_below/point_under_edge [in X in X || _]sameright.
rewrite (eqP (proj1 (proj2 (pue_formula_two_points _ _)))) lexx /=.
rewrite /point_strictly_under_edge -[in X in _ || X]sameright -!leNgt.
rewrite (eqP (proj1 (proj2 (pue_formula_two_points _ _)))) lexx /= !andbT.
rewrite !pue_formulaE !(proj2 (pue_f_eq_slopes _ _ _ _ _ _)).
rewrite /cmp_slopes sameright oppr_le0 opprB.
rewrite !(mulrC (p_y (right_pt e2) - _)) orbb.
by rewrite sgr_le0 -oppr_ge0 [X in _ = (0 <= X)]opprB.
Qed.

Definition slope e :=
  (p_y (right_pt e) - p_y (left_pt e)) / (p_x (right_pt e) - p_x (left_pt e)).

Lemma cmp_slopesE e1 e2 :
  cmp_slopes e1 e2 = sg(slope e2 - slope e1).
Proof.
have := edge_cond e1.
  rewrite -subr_gt0 =>/gtr0_sg den1.
have := edge_cond e2.
  rewrite -subr_gt0 =>/gtr0_sg den2.
rewrite -[RHS]mul1r -den1 -[RHS]mul1r -den2 -!sgrM.
rewrite [X in sg( _ * X)]mulrBr /slope.
rewrite [X in sg(X)]mulrBr 2![in X in sg(X - _)]mulrA.
rewrite [X in sg( X * _ * _ - _)]mulrC.
rewrite 2![in X in sg(_ - X)]mulrA.
rewrite /cmp_slopes.
set V := (p_x (right_pt e1) - _).
set W := (p_x (right_pt e2) - _).
set U := (p_y _ - _).
set Z := (p_y _ - _).
have den20 : W != 0 by rewrite -sgr_eq0 den2.
have den10 : V != 0 by rewrite -sgr_eq0 den1.
by rewrite (mulrAC V) mulfK // (mulrAC W) mulfK // (mulrC U) (mulrC Z).
Qed.

Lemma on_edge_same_slope_right e1 e1' :
  left_pt e1' === e1 -> right_pt e1 = right_pt e1' ->
  slope e1' = slope e1.
Proof.
move=> /andP[]+ val eqr.
rewrite pue_formula_opposite pue_formula_cycle oppr_eq0.
rewrite pue_formulaE (proj1 (pue_f_eq_slopes _ _ _ _ _ _)).
have := edge_cond e1.
  rewrite -subr_gt0 => den1.
have := edge_cond e1'.
  rewrite -subr_gt0 => den1'.
rewrite subr_eq0.
set W := (p_x _ - _).
set V := (p_x _ - _).
have den10 : W != 0.
  by rewrite subr_eq0 eq_sym -subr_eq0 lt0r_neq0 // den1.
have den10v : W ^-1 != 0 by rewrite invr_eq0.
have den20 : V != 0.
  by rewrite subr_eq0 eq_sym -subr_eq0 lt0r_neq0 // eqr den1'.
have den20v : V ^-1 != 0 by rewrite invr_eq0.
rewrite -(inj_eq (mulIf den10v)) mulfK //.
rewrite -(inj_eq (mulfI den20v)) 2!mulrA 2!(mulrC V ^-1) divff // mul1r.
rewrite -[X in X / V]opprB mulNr -mulrN -invrN /V opprB.
rewrite -[X in X / W]opprB mulNr -mulrN -invrN /V opprB.
by rewrite /slope eqr=> /eqP.
Qed.

Lemma on_edge_same_slope_left e1 e1' :
  right_pt e1' === e1 -> left_pt e1 = left_pt e1' ->
  slope e1' = slope e1.
Proof.
move=> /andP[]+ val eqr.
rewrite pue_formulaE (proj1 (pue_f_eq_slopes _ _ _ _ _ _)).
have := edge_cond e1.
  rewrite -subr_gt0 => den1.
have := edge_cond e1'.
  rewrite -subr_gt0 => den1'.
rewrite subr_eq0.
set W := (p_x _ - _).
set V := (p_x _ - _).
have den10 : W != 0.
  by rewrite subr_eq0 -subr_eq0 lt0r_neq0 // den1.
have den10v : W ^-1 != 0 by rewrite invr_eq0.
have den20 : V != 0.
  by rewrite subr_eq0 -subr_eq0 lt0r_neq0 // eqr den1'.
have den20v : V ^-1 != 0 by rewrite invr_eq0.
rewrite -(inj_eq (mulIf den10v)) mulfK //.
rewrite -(inj_eq (mulfI den20v)) 2!mulrA 2!(mulrC V ^-1) divff // mul1r.
by rewrite /slope /W /V eqr=> /eqP.
Qed.

Lemma cmp_slopesNC e1 e2 : -cmp_slopes e1 e2 = cmp_slopes e2 e1.
Proof. by rewrite /cmp_slopes -sgrN [in LHS]opprB. Qed.

Lemma contact_left_slope e1 e2 :
  left_pt e1 === e2 -> 
  (right_pt e1 <<= e2) = (0 <= cmp_slopes e1 e2) /\
  (right_pt e1 <<< e2) = (0 < cmp_slopes e1 e2).
Proof.
move=> /[dup] on2 /andP[] form val.
suff pue_formula_eq :
  sg (pue_formula (right_pt e1) (left_pt e2) (right_pt e2)) =
  -(cmp_slopes e1 e2).
  rewrite /point_under_edge /point_strictly_under_edge.
  rewrite -sgr_le0 pue_formula_eq oppr_le0 sgr_ge0; split;[by [] |].
  by rewrite -sgr_lt0 pue_formula_eq oppr_lt0 sgr_gt0.
move: (val) => /andP[] _; rewrite le_eqVlt=> /orP[/eqP atr | le1ltre2].
  rewrite /cmp_slopes atr.
  have eqps : left_pt e1 = right_pt e2.
    have := on_edge_same_point (right_on_edge _) on2.
    rewrite atr eqxx => /(_ isT) /eqP; move: (right_pt e2) (left_pt e1) atr.
    by move=> [] ? ? [] ? ? /= -> ->.
  rewrite pue_formula_opposite pue_formula_cycle.
  rewrite sgrN.
  rewrite !pue_formulaE !(proj1 (pue_f_eq_slopes _ _ _ _ _ _)).
  rewrite -eqps -(mulrC (p_y _ - _)).
  rewrite -[X in _ = - sg (X * _ - _)]opprB -[X in _ = - sg (_ -  _ * X)]opprB.
  by rewrite mulrN mulNr -opprD opprB.
set e2' := Bedge le1ltre2.
have signcond := pue_formula_change_ext (right_pt e1) (edge_cond e2) le1ltre2
             form (proj1 (proj2 (pue_formula_two_points _ _))).
rewrite {}signcond.
have on2' : left_pt e2' === e2 by exact: on2.
rewrite cmp_slopesE  -(on_edge_same_slope_right on2')// -cmp_slopesE.
rewrite cmp_slopesNC.
rewrite pue_formulaE (proj1 (pue_f_eq_slopes _ _ _ _ _ _)) /cmp_slopes.
by rewrite /e2' /= [in LHS](mulrC (p_x _ - _)).
Qed.

Lemma contact_right_slope e1 e2 :
  right_pt e1 === e2 -> 
  (left_pt e1 <<= e2) = (cmp_slopes e1 e2 <= 0) /\
  (left_pt e1 <<< e2) = (cmp_slopes e1 e2 < 0).
Proof.
move=> /[dup] on2 /andP[] form val.
suff pue_formula_eq :
  sg (pue_formula (left_pt e1) (left_pt e2) (right_pt e2)) =
  cmp_slopes e1 e2.
  rewrite /point_under_edge /point_strictly_under_edge.
  rewrite -pue_formula_eq -[X in X = _ /\ _]sgr_le0; split; first by [].
  by rewrite -[LHS]sgr_lt0.
move: (val) => /andP[] + _; rewrite le_eqVlt eq_sym=> /orP[/eqP atl | le2ltre1].
  rewrite /cmp_slopes atl.
  have eqps : right_pt e1 = left_pt e2.
    have := on_edge_same_point (left_on_edge _) on2.
    rewrite atl eqxx => /(_ isT) /eqP; move: (right_pt e1) (left_pt e2) atl.
    by move=> [] ? ? [] ? ? /= -> ->.
  rewrite !pue_formulaE !(proj1 (pue_f_eq_slopes _ _ _ _ _ _)).
  rewrite eqps (mulrC (p_x _ - _)).
  rewrite -[X in _ = sg (_ * X - _)]opprB -[X in _ = sg (_ -  X * _)]opprB.
  by rewrite mulrN mulNr -opprD opprB.
set e2' := Bedge le2ltre1.
have signcond := pue_formula_change_ext (left_pt e1) (edge_cond e2) le2ltre1
             (proj1 (pue_formula_two_points _ _)) form.
rewrite {}signcond.
have on2' : right_pt e2' === e2 by exact: on2.
rewrite cmp_slopesE  -(on_edge_same_slope_left on2')// -cmp_slopesE.
rewrite pue_formula_opposite pue_formula_cycle.
rewrite pue_formulaE (proj1 (pue_f_eq_slopes _ _ _ _ _ _)) /cmp_slopes.
rewrite /e2' /= [in LHS](mulrC (p_x _ - _)) opprB.
by rewrite -4![in LHS](opprB (_ (right_pt e1))) 2!mulrNN.
Qed.

Lemma sub_edge_right (p : pt) (e : edge) : p === e ->
  p_x p < p_x (right_pt e) ->
  {e' | [/\ left_pt e' = p, right_pt e' = right_pt e &
        forall e2, cmp_slopes e' e2 = cmp_slopes e e2]}.
Proof.
move=>/[dup] one /andP[] aligned val dif; exists (Bedge dif).
split => // e2; rewrite !cmp_slopesE.
by rewrite (@on_edge_same_slope_right e (Bedge dif) one erefl).
Qed.

Lemma sub_edge_left (p : pt) (e : edge) : p === e ->
  p_x (left_pt e) < p_x p ->
  {e' | [/\ left_pt e' = left_pt e, right_pt e' = p &
        forall e2, cmp_slopes e' e2 = cmp_slopes e e2]}.
Proof.
move=>/[dup] one /andP[] aligned val dif; exists (Bedge dif).
split => // e2; rewrite !cmp_slopesE.
by rewrite (@on_edge_same_slope_left e (Bedge dif) one erefl).
Qed.

Lemma intersection_imp_crossing e1 e2 p :
  p === e1 -> p === e2 ->
  p_x (left_pt e1) < p_x p -> p_x p < p_x (right_pt e1) ->
  p_x (left_pt e2) < p_x p -> p_x p < p_x (right_pt e2) ->
  ~below_alt e1 e2 \/ cmp_slopes e1 e2 == 0.
Proof.
move=> on1 on2 l1ltp pltr1 l2ltp pltr2.
have [e2' [le2' re2' sle2']] := sub_edge_left on2 l2ltp.
have [e2'' [le2'' re2'' sle2'']] := sub_edge_right on2 pltr2.
have [e1' [le1' re1' sle1']] := sub_edge_left on1 l1ltp.
have [e1'' [le1'' re1'' sle1'']] := sub_edge_right on1 pltr1.
have /contact_left_slope/= : left_pt e2'' === e1 by rewrite le2''.
have /contact_right_slope/= : right_pt e2' === e1 by rewrite re2'.
have /contact_left_slope/= : left_pt e1'' === e2 by rewrite le1''.
have /contact_right_slope/= : right_pt e1' === e2 by rewrite re1'.
rewrite le1' le2' re2'' re1'' sle1' sle1'' sle2' sle2'' -(cmp_slopesNC e1).
rewrite !oppr_lte0 !oppr_gte0 => -[]D' D []C' C []B' B []A' A.
rewrite /below_alt/edge_below.
have [ | difslope] := boolP(cmp_slopes e1 e2 == 0); first by right.
left; rewrite D' C' A B A' B' D C -!leNgt orbC=> /orP; rewrite andbC !orbb.
by move/le_anti/esym/eqP; rewrite (negbTE difslope).
Qed.

Lemma edge_below_equiv p (s : pred edge) :
  {in s, forall e, valid_edge e p && (p_x p < p_x (right_pt e))} ->
  {in s &, no_crossing} ->
  {in s & , forall e1 e2: edge, (e1 <| e2) = pedge_below p e1 e2}.
Proof.
move=> val noc e1 e2.
move=> /[dup] e1in /val /andP[] /[dup] ve1 /exists_point_valid [p1 p1P] re1.
move: (p1P); rewrite (pvertE ve1) =>/esym[] p1q.
move: (ve1)=> /pvert_on; rewrite -p1q=> on1.
move=> /[dup] e2in /val /andP[] /[dup] ve2 /exists_point_valid [p2 p2P] re2.
move: (p2P); rewrite (pvertE ve2) =>/esym[] p2q.
move: (ve2)=> /pvert_on; rewrite -p2q=> on2; rewrite /pedge_below.
have p1p2 : p_x p1 = p_x p2 by rewrite p1q p2q.
have [vylt /= | vylt' /= | vyq] := ltrgtP.
- case: (noc e1 e2 e1in e2in) => // abs.
  have := order_below_viz_vertical ve2 ve1 p2P p1P abs; rewrite leNgt.
  by rewrite p1q p2q /= vylt.
- have re1' : p_x p1 < p_x (right_pt e1) by rewrite p1q.
  have p2u : p2 <<< e1.
    by rewrite (strict_under_edge_lower_y (esym p1p2)); rewrite // p2q p1q.
  have p1a : p1 >>> e2.
    by rewrite (under_edge_lower_y p1p2); rewrite // -ltNge p2q p1q.
  apply/negP=> /orP[|] /andP[]leftc rightc.
    by move: p1a; rewrite (point_on_edge_under _ leftc rightc) // p1q.
  move: p2u; rewrite -(negbK (_ <<< _)).
  by rewrite (point_on_edge_above _ leftc rightc) // p2q.
have pp : p1 = p2 by rewrite p1q p2q vyq.
move: (ve1) => /andP[] + _; rewrite le_eqVlt=>/orP[/eqP pleft | pmid] /=.
  have p1l : p1 = left_pt e1.
    apply/esym/eqP; rewrite pt_eqE.
    by rewrite (on_edge_same_point (left_on_edge _) on1) pleft p1q eqxx.
  move: ve2 => /andP[] + _; rewrite le_eqVlt=> /orP [/eqP pleft2 | pmid2].
    have p2l : p2 = left_pt e2.
      apply/esym/eqP; rewrite pt_eqE.
      by rewrite (on_edge_same_point (left_on_edge _) on2) pleft2 p2q eqxx.
    by apply: same_left_edge_below_slopes; rewrite -p1l pp.
  have le2ltp2 : p_x (left_pt e2) < p_x p2 by rewrite p2q.
  have [e2' [le2' re2' sle2']] := sub_edge_left on2 le2ltp2.
  have re2'e1 : right_pt e2' === e1 by rewrite re2' -pp.
  rewrite /edge_below.
  have := (contact_right_slope re2'e1) => /= -[] _; rewrite le2' sle2' => ->.
  have p2ltre2 : p_x p2 < p_x (right_pt e2) by rewrite p2q.
  have [e2'' [le2'' re2'' sle2'']] := sub_edge_right on2 p2ltre2.
  have le2''e1 : left_pt e2'' === e1 by rewrite le2'' -pp.
  have := (contact_left_slope le2''e1) => -[] _; rewrite re2'' sle2'' => ->.
  rewrite -2!leNgt.
  set W := (X in _ || X); have [ | difslope] := boolP W.
    rewrite {}/W=>/le_anti/esym/eqP.
    by rewrite -cmp_slopesNC oppr_eq0 orbT=> /eqP->.
  rewrite orbF -p1l pp {1}/point_under_edge; move: (on2); rewrite /point_on_edge.
  move=> /andP[] /eqP -> _; rewrite lexx /=.
  by move: (on2); rewrite -pp p1l=>/contact_left_slope=>-[].
have le1ltp1 : p_x (left_pt e1) < p_x p1 by rewrite p1q.
have [e1' [le1' re1' sle1']] := sub_edge_left on1 le1ltp1.
have re1'e2 : right_pt e1' === e2 by rewrite re1' pp.
rewrite /edge_below.
set W := (X in X || _); set W' := (X in _ || X).
have := (contact_right_slope re1'e2); rewrite le1' sle1' => /= -[] eq1 _.
have p1ltre1 : p_x p1 < p_x (right_pt e1) by rewrite p1q.
have [e1'' [le1'' re1'' sle1'']] := sub_edge_right on1 p1ltre1.
have le1''e2 : left_pt e1'' === e2 by rewrite le1'' pp.
have /= := (contact_left_slope le1''e2); rewrite re1'' sle1'' => - [] /= eq2 _.
have Weq : W = (cmp_slopes e1 e2 == 0).
  rewrite /W eq1 eq2; apply/idP/eqP; first by apply/le_anti.
  by move=> ->; rewrite lexx.
have [ | difslope /=] := boolP W.
  by rewrite /= le_eqVlt Weq => /eqP ->; rewrite eqxx.
rewrite le_eqVlt eq_sym -Weq (negbTE difslope) /=.
move: (ve2) => /andP[] + _; rewrite le_eqVlt => /orP [/eqP l2p | l2ltp].
  have /eqP p2l : left_pt e2 == p1.
    rewrite pt_eqE.
    rewrite (eqP (on_edge_same_point (left_on_edge _) on2 _)) -pp l2p p1q //=.
    by rewrite !eqxx.
  have/contact_left_slope[_ eq3] : left_pt e2 === e1 by rewrite p2l.
  move: on1=>/andP[] /eqP + _; rewrite -p2l => eq4.
  rewrite /W' eq3 lt_neqAle -cmp_slopesNC eq_sym oppr_eq0 -Weq difslope andTb.
  by rewrite -leNgt eq4 lexx -ltNge oppr_lt0.
have xpp1 : p_x p = p_x p1 by rewrite p1q.
move: on2 l2ltp re2; rewrite -pp xpp1 => on2 l2ltp re2.
have := intersection_imp_crossing on1 on2 le1ltp1 p1ltre1 l2ltp re2=> -[[]|abs].
  by apply: noc.
by case/negP: difslope; rewrite Weq.
Qed.

Lemma edge_below_equiv' p (s : pred edge) :
  {in s, forall e, valid_edge e p && (p_x (left_pt e) < p_x p)} ->
  {in s &, no_crossing} ->
  {in s & , forall e1 e2: edge, (e1 <| e2) = pedge_below' p e1 e2}.
Proof.
move=> val noc e1 e2.
move=> /[dup] e1in /val /andP[] /[dup] ve1 /exists_point_valid [p1 p1P] le1.
move: (p1P); rewrite (pvertE ve1) =>/esym[] p1q.
move: (ve1)=> /pvert_on; rewrite -p1q=> on1.
move=> /[dup] e2in /val /andP[] /[dup] ve2 /exists_point_valid [p2 p2P] le2.
move: (p2P); rewrite (pvertE ve2) =>/esym[] p2q.
move: (ve2)=> /pvert_on; rewrite -p2q=> on2; rewrite /pedge_below'.
have p1p2 : p_x p1 = p_x p2 by rewrite p1q p2q.
have [vylt /= | vylt' /= | vyq] := ltrgtP.
- case: (noc e1 e2 e1in e2in) => // abs.
  have := order_below_viz_vertical ve2 ve1 p2P p1P abs; rewrite leNgt.
  by rewrite p1q p2q /= vylt.
- have le1' : p_x (left_pt e1) < p_x p1 by rewrite p1q.
  have p2u : p2 <<< e1.
    by rewrite (strict_under_edge_lower_y (esym p1p2)); rewrite // p2q p1q.
  have p1a : p1 >>> e2.
    by rewrite (under_edge_lower_y p1p2); rewrite // -ltNge p2q p1q.
  apply/negP=> /orP[|] /andP[]leftc rightc.
    by move: p1a; rewrite (point_on_edge_under _ leftc rightc) // p1q.
  move: p2u; rewrite -(negbK (_ <<< _)).
  by rewrite (point_on_edge_above _ leftc rightc) // p2q.
have pp : p1 = p2 by rewrite p1q p2q vyq.
move: (ve1) => /andP[] _ +; rewrite le_eqVlt=>/orP[/eqP pright | pmid] /=.
  have p1r : p1 = right_pt e1.
    apply/eqP; rewrite pt_eqE.
    by rewrite (on_edge_same_point on1 (right_on_edge _)) -pright p1q eqxx.
  move: ve2 => /andP[] _; rewrite le_eqVlt=> /orP [/eqP pright2 | pmid2].
    have p2l : p2 = right_pt e2.
      apply/eqP; rewrite pt_eqE.
      by rewrite (on_edge_same_point on2 (right_on_edge _)) -pright2 p2q eqxx.
    by apply: same_right_edge_below_slopes; rewrite -p1r pp.
  have p2ltre2 : p_x p2 < p_x (right_pt e2) by rewrite p2q.
  have [e2' [le2' re2' sle2']] := sub_edge_right on2 p2ltre2.
  have le2'e1 : left_pt e2' === e1 by rewrite le2' -pp.
  rewrite /edge_below.
  have := (contact_left_slope le2'e1) => /= -[] _; rewrite re2' sle2' => ->.
  have le2ltp2 : p_x (left_pt e2) < p_x p2 by rewrite p2q.
  have [e2'' [le2'' re2'' sle2'']] := sub_edge_left on2 le2ltp2.
  have re2''e1 : right_pt e2'' === e1 by rewrite re2'' -pp.
  have := (contact_right_slope re2''e1) => -[] _; rewrite le2'' sle2'' => ->.
  rewrite -2!leNgt.
  set W := (X in _ || X); have [ | difslope] := boolP W.
    rewrite {}/W=>/le_anti/esym/eqP.
    by rewrite -cmp_slopesNC oppr_eq0 orbT=> /eqP->.
  rewrite orbF -p1r pp {2}/point_under_edge; move: (on2); rewrite /point_on_edge.
  move=> /andP[] /eqP -> _; rewrite lexx andbT.
  by move: (on2); rewrite -pp p1r=>/contact_right_slope=>-[].
have p1ltre1 : p_x p1 < p_x (right_pt e1) by rewrite p1q.
have [e1' [le1' re1' sle1']] := sub_edge_right on1 p1ltre1.
have le1'e2 : left_pt e1' === e2 by rewrite le1' pp.
rewrite /edge_below.
set W := (X in X || _); set W' := (X in _ || X).
have := (contact_left_slope le1'e2); rewrite re1' sle1' => /= -[] eq1 _.
have le1ltp1 : p_x (left_pt e1) < p_x p1 by rewrite p1q.
have [e1'' [le1'' re1'' sle1'']] := sub_edge_left on1 le1ltp1.
have re1''e2 : right_pt e1'' === e2 by rewrite re1'' pp.
have /= := (contact_right_slope re1''e2); rewrite le1'' sle1'' => - [] /= eq2 _.
have Weq : W = (cmp_slopes e1 e2 == 0).
  rewrite /W eq1 eq2; apply/idP/eqP; first by apply/le_anti.
  by move=> ->; rewrite lexx.
have [ | difslope /=] := boolP W.
  by rewrite /= le_eqVlt Weq => /eqP ->; rewrite eqxx.
rewrite le_eqVlt -Weq (negbTE difslope) /=.
move: (ve2) => /andP[] _; rewrite le_eqVlt => /orP [/eqP r2p | pltr2].
  have /eqP p2r : right_pt e2 == p1.
    rewrite pt_eqE.
    rewrite -(eqP (on_edge_same_point on2 (right_on_edge _) _)) -pp -r2p p1q //=.
    by rewrite !eqxx.
  have/contact_right_slope[_ eq3] : right_pt e2 === e1 by rewrite p2r.
  move: on1=>/andP[] /eqP + _; rewrite -p2r => eq4.
  rewrite /W' eq3 lt_neqAle -cmp_slopesNC oppr_eq0 -Weq difslope andTb.
  by rewrite /W' /point_strictly_under_edge eq4 ltxx andbT -ltNge oppr_gt0.
have xpp1 : p_x p = p_x p1 by rewrite p1q.
move: on2 pltr2 le2; rewrite -pp xpp1 => on2 pltr2 le2.
have := intersection_imp_crossing on1 on2 le1ltp1 p1ltre1 le2 pltr2=> -[[]|abs].
  by apply: noc.
by case/negP: difslope; rewrite Weq.
Qed.

Lemma pedge_below_trans p: transitive (pedge_below p).
Proof.
move=> e2 e1 e3; rewrite /pedge_below.
move=>/orP[v12 | /andP [y12 s12]] /orP[v23 | /andP[y23 s23]].
- by rewrite (lt_trans v12 v23).
- by rewrite -(eqP y23) v12.
- by rewrite (eqP y12) v23.
rewrite orbC (eqP y12) y23.
move: s12 s23; rewrite !cmp_slopesE !sgr_ge0 !subr_ge0=> s12 s23.
by rewrite (le_trans s12 s23).
Qed.

Lemma pedge_below_trans' p: transitive (pedge_below' p).
Proof.
move=> e2 e1 e3; rewrite /pedge_below'.
move=>/orP[v12 | /andP [y12 s12]] /orP[v23 | /andP[y23 s23]].
- by rewrite (lt_trans v12 v23).
- by rewrite -(eqP y23) v12.
- by rewrite (eqP y12) v23.
rewrite orbC (eqP y12) y23.
move: s12 s23; rewrite !cmp_slopesE !sgr_le0.
rewrite (subr_le0 (slope e1)) (subr_le0 (slope e2)) (subr_le0 (slope e1)).
by move=> s12 s23; rewrite (le_trans s23 s12).
Qed.

Lemma edge_below_trans p (s : pred edge) :
  {in s, forall e, p_x p < p_x (right_pt e)} \/ 
  {in s, forall e, p_x (left_pt e) < p_x p} ->
  {in s, forall e, valid_edge e p} -> {in s &, no_crossing} ->
  {in s & & , transitive edge_below}.
Proof.
move=> [rbound | lbound] vals noc e2 e1 e3 e2in e1in e3in.
  have valb : {in s, forall e, valid_edge e p && (p_x p < p_x (right_pt e))}.
    by move=> e ein; apply/andP; split;[apply: vals | apply: rbound].
  rewrite (edge_below_equiv valb noc) // (edge_below_equiv valb noc) //.
  rewrite (edge_below_equiv valb noc) //.
  by apply: pedge_below_trans.
have valb : {in s, forall e, valid_edge e p && (p_x (left_pt e) < p_x p)}.
  by move=> e ein; apply/andP; split;[apply: vals | apply: lbound].
rewrite (edge_below_equiv' valb noc) // (edge_below_equiv' valb noc) //.
rewrite (edge_below_equiv' valb noc) //.
by apply: pedge_below_trans'.
Qed.

Lemma seq_edge_below s c :
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) ->
  path edge_below (head dummy_edge [seq low i | i <- rcons s c])
     [seq high i | i <- rcons s c].
Proof.
elim: s => [ | c0 s Ih] // /[dup]/= /adjacent_cons adj' adj /andP[] rfc rfo.
apply/andP;split;[exact: rfc | ].
have -> : high c0 = head dummy_edge [seq low i | i <- rcons s c].
  by move: adj; case: (s) => [ | c1 q]; rewrite //= => /andP[] /eqP -> _.
by apply: Ih.
Qed.

Lemma below_seq_higher_edge s c e p evs :
  {in [seq high i | i <- rcons s c] & & ,transitive edge_below} ->
  p_x e <= p_x p ->
  {in evs, forall ev, lexPt p (point ev)} ->
  inside_box p ->
  {in evs, forall ev, lexPt e (point ev)} ->
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) -> 
  seq_valid (rcons s c) e -> close_alive_edges (rcons s c) evs ->
  {in [seq high i | i <- rcons s c] &, no_crossing} ->
  {in rcons s c, forall c1, strict_inside_open p c1 -> p <<< high c}.
Proof.
move=> + lboundp rboundp inbox_p lexe.
elim: s => [ | c0 s Ih].
  rewrite /= ?andbT => /= _ _ rfc sval clae noc c1.
  by rewrite inE=> /eqP -> /andP[] /andP[].
rewrite -[rcons _ _]/(c0 :: rcons s c)=> e_trans /[dup]/adjacent_cons adj'.
rewrite /= => adj /[dup] rf0 /andP[rfc0 rfo] sval clae noc.
move=> c1 c1in /[dup] pinc1 /andP[] /andP[] puhc1 _ lims.
have ende g : valid_edge g e -> end_edge g evs -> valid_edge g p.
  move=>vge /orP[|/hasP[ev' evin /eqP cl]].
    by apply: inside_box_valid_bottom_top.
  move: vge=>/andP[]lge _.
  rewrite /valid_edge (le_trans lge lboundp) /= cl lexePt_xW // lexPtW //.
  by apply: rboundp.
have v0p : valid_edge (high c0) p.
  apply: ende; first by move:sval=>/andP[]/andP[].
  by move: clae=>/andP[]/andP[].
have vcell c2 : c2 \in rcons s c -> valid_edge (high c2) p.
  move=> c2in; move: clae=>/andP[] _ /allP/(_ c2 c2in)/andP[] _ ec.
  by move: sval=>/andP[] _ /allP/(_ c2 c2in)/andP[] _ vce; apply: ende.
have vcp : valid_edge (high c) p by apply: vcell; rewrite mem_rcons inE eqxx.
have hc0below : high c0 <| high c.
  have highhead : high c0 = head dummy_edge [seq low i | i <- rcons s c].
    by case: (s) adj => [ /= | a b /=]/andP[]/eqP ->.
  have := seq_edge_below adj' rfo; rewrite -highhead.
  have := path_sorted_inE e_trans => ->; last by apply/allP=> x xin; exact: xin.
  move=> /andP[]/allP/(_ (high c)) + _; apply.
  by apply: map_f; rewrite mem_rcons inE eqxx.
move:c1in; rewrite /= inE => /orP[/eqP c1c0 | intail].
  by apply: (order_edges_strict_viz_point' v0p vcp hc0below); rewrite -c1c0.
have tr' : {in [seq high i | i <- rcons s c] & &, transitive edge_below}.
  move=> g1 g2 g3 g1in g2in g3in.
  by apply: e_trans; rewrite inE ?g1in ?g2in ?g3in orbT.
have sval' : seq_valid (rcons s c) e by case/andP: sval.
have clae' : close_alive_edges (rcons s c) evs by case/andP: clae.
have noc' : {in [seq high i | i <- rcons s c] &, no_crossing}.
  by move=> g1 g2 g1in g2in; apply: noc; rewrite !inE ?g1in ?g2in orbT.
apply: (Ih tr' adj' rfo sval' clae' noc' c1 intail pinc1).
Qed.

Definition open_cell_side_limit_ok c :=
  [&& left_pts c != [::],
   all (fun p => p_x p == p_x (last dummy_pt (left_pts c))) (left_pts c),
  sorted >%R [seq p_y p | p <- left_pts c],
  (head dummy_pt (left_pts c) === high c) &
  (last dummy_pt (left_pts c) === low c)].

Lemma left_pt_above g : left_pt g >>= g.
Proof.
rewrite /point_strictly_under_edge (eqP (proj1 (pue_formula_two_points _ _))).
by rewrite ltxx.
Qed.

Lemma right_pt_above g : right_pt g >>= g.
Proof.
rewrite /point_strictly_under_edge.
by rewrite (eqP (proj1 (proj2 (pue_formula_two_points _ _)))) ltxx.
Qed.

Lemma left_pt_below g : left_pt g <<= g.
Proof.
rewrite /point_under_edge (eqP (proj1 (pue_formula_two_points _ _))).
by rewrite lexx.
Qed.

Lemma right_pt_below g : right_pt g <<= g.
Proof.
rewrite /point_under_edge.
by rewrite (eqP (proj1 (proj2 (pue_formula_two_points _ _)))) lexx.
Qed.

Lemma opening_cells_side_limit e s le he :
  valid_edge le e -> valid_edge he e -> le <| he ->
  e >>= le -> e <<< he ->
  {in [:: le, he & s] &, no_crossing} ->
  {in s, forall g, left_pt g == e} ->
  all open_cell_side_limit_ok (opening_cells e s le he).
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
suff/allP/(_ c cintl) : all open_cell_side_limit_ok (opening_cells e s g he).
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

Lemma opening_cells_below_high p e c s le he:
  le <| he ->
  (e >>> le) && (e <<< he) ->
  valid_edge le e ->
  valid_edge he e ->
  valid_edge he p -> (forall g, g \in s -> left_pt g == e) ->
  {in le::he::s &, no_crossing} ->
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
  {in le:: he :: s &, no_crossing} ->
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

Lemma left_side_below_seq_higher_edge s c e p evs :
  p_x e <= p_x p ->
  {in evs, forall ev, lexPt p (point ev)} ->
  inside_box p ->
  {in evs, forall ev, lexPt e (point ev)} ->
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) ->
  seq_valid (rcons s c) e -> close_alive_edges (rcons s c) evs ->
  {in [seq high i | i <- rcons s c], forall g, p_x (left_pt g) < p_x e} ->
  {in [seq high i | i <- rcons s c] &, no_crossing} ->
  {in rcons s c, forall c1, strict_inside_open p c1 -> p <<< high c}.
Proof.
move => lboundp rboundp inboxp evc adj rfs svals clae llim noc c1 c1in.
apply: (below_seq_higher_edge _ _ _ _ _ _ _ svals clae noc c1in) => //.
have vale' : {in [seq high i | i <- rcons s c], forall g, valid_edge g e}.
  by move=> g /mapP [c' c'in ->]; move: (allP svals c' c'in)=>/andP[].
apply: (edge_below_trans _ vale' noc); right; exact: llim.
Qed.

Lemma right_side_below_seq_higher_edge s c e p evs :
  p_x e <= p_x p ->
  {in evs, forall ev, lexPt p (point ev)} ->
  inside_box p ->
  {in evs, forall ev, lexPt e (point ev)} ->
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) -> 
  seq_valid (rcons s c) e -> close_alive_edges (rcons s c) evs ->
  {in [seq high i | i <- rcons s c], forall g, p_x e < p_x (right_pt g)} ->
  {in [seq high i | i <- rcons s c] &, no_crossing} ->
  {in rcons s c, forall c1, strict_inside_open p c1 -> p <<< high c}.
Proof.
move => lboundp rboundp inboxp evc adj rfs svals clae rlim noc c1 c1in.
apply: (below_seq_higher_edge _ _ _ _ _ _ _ svals clae noc c1in) => //.
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

Lemma seq_edge_below' s :
  adjacent_cells s -> s_right_form s ->
  path edge_below (head dummy_edge [seq low i | i <- s])
     [seq high i | i <- s].
Proof.
elim: s => [ | c0 s Ih] // /[dup]/= /adjacent_cons adj' adj /andP[] rfc rfo.
apply/andP;split;[exact: rfc | ].
case sq : s => [// | c1 s'].
have -> : high c0 = head dummy_edge [seq low i | i <- c1 :: s'].
  by move: adj; rewrite sq /= => /andP[] /eqP.
by rewrite -sq; apply: Ih.
Qed.

Lemma opening_cells_disjoint (s oe : seq edge) p le he :
    p >>> le -> p <<< he -> le \in s -> he \in s -> le <| he ->
    valid_edge le p -> valid_edge he p -> {subset oe <= s} ->
    {in s &, no_crossing} -> {in oe, forall g : edge, left_pt g == p} ->
    path edge_below le oe ->
    {in opening_cells p oe le he &, disjoint_open_cells}.
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
suff main : forall c, c \in opening_cells p oe og he -> o_disjoint_e W c.
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
have oc0q : opening_cells p (og :: oe) le he = W :: opening_cells p oe og he.
  by rewrite /= vip.
have noc' : {in [:: le, he , og & oe] &, no_crossing}.
  move: noc; apply: sub_in2 => g; rewrite 2!inE.
  by move=> /orP[/eqP ->| /orP[/eqP -> | ginoe]] //; apply: oesub.
have/allP cok := opening_cells_side_limit vl vh lowhigh pl ph noc' leftg.
have [/andP[]/andP[] Main w lims/= | qnW//] := boolP(strict_inside_open q W).
have vhwq : valid_edge (high W) q.
  apply: valid_high_limits => //.
  by apply: cok; rewrite oc0q inE eqxx.
have adj0 := adjacent_opening' p (og :: oe) le he.
have rf0 := opening_cells_right_form' pl ph vh lein hein lowhigh leftg noc
         oesub soe erefl.
have := seq_edge_below' adj0 rf0; rewrite oc0q [head _ _]/= => srt.
have vog : valid_edge og q by move: vhwq; rewrite [high W]/=.
case ocq : (opening_cells p oe og he) => [| c0 q0].
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
have tr : {in (og :: oe) & & , transitive edge_below}.
  apply: (@edge_below_trans p); last by move: noc; apply: sub_in2.
    by left; move=> g gin; rewrite -(eqP (leftg g gin)) edge_cond.
  by move=> g gin; apply: valid_edge_extremities; rewrite leftg ?eqxx.
have  : all (mem (og :: oe)) [seq low i | i <- opening_cells p oe og he].
  apply/allP=> g /mapP [c2 c2p1 ->].
  by have := opening_cells_subset c2p1=> /andP[].
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
  move: rf0; rewrite /right_form => lowhigh.
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
  rewrite /right_form /open_cell_side_limit_ok => lowhigh /andP[] ln0.
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

Lemma sorted_outgoing le he e : 
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  point e >>> le ->
  point e <<< he ->
  out_left_event e ->
  {in le :: he :: outgoing e &, no_crossing} ->
  sorted edge_below (le :: sort edge_below (outgoing e)).
Proof.
 set ctxt := (le :: he :: _); move=> vl hl above under outs noc.
have lein : le \in ctxt by rewrite /ctxt inE eqxx.
have hein : he \in ctxt by rewrite /ctxt !inE eqxx ?orbT.
have osub : {subset outgoing e <= ctxt}.
  by move=> g gin; rewrite /ctxt !inE gin ?orbT.
have [ls us noc''] :=
   outgoing_conditions above under lein hein vl hl osub noc outs.
have /sort_sorted_in tmp : {in le :: outgoing e &, total edge_below}.
  move=> e1 e2; rewrite !inE =>/orP[/eqP -> |e1in ]/orP[/eqP -> |e2in].
  - by rewrite edge_below_refl.
  - by rewrite ls.
  - by rewrite ls ?orbT.
  by apply/orP/noc''.
rewrite /=; case oeq : (sort edge_below (outgoing e)) => [// | g1 gs] /=.
rewrite ls; last first.
  have <- := perm_mem (permEl (perm_sort edge_below (outgoing e))).
  by rewrite oeq inE eqxx.
rewrite -[X in is_true X]/(sorted _ (g1 :: gs)) -oeq tmp //.
by apply/allP=> x xin /=; apply/orP; right; exact: xin.
Qed.

Definition any_edge (b : bool) (c : cell) : edge :=
  if b then low c else high c.

Lemma first_cells_right_pt fc ev events :
  close_alive_edges fc events ->
  inside_box (point ev) ->
  all (fun x => lexPtEv  ev x) events ->
  {in fc, forall c b, lexPt (point ev) (right_pt (any_edge b c))}.
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

Lemma under_pvert_y (p : pt) (e : edge) :
  valid_edge e p -> (p <<= e) = (p_y p <= pvert_y p e).
Proof.
move=> val.
have xs : p_x p = p_x (Bpt (p_x p) (pvert_y p e)) by [].
have one : Bpt (p_x p) (pvert_y p e) === e by apply: pvert_on.
by rewrite (under_edge_lower_y xs one).
Qed.

Lemma strict_under_pvert_y (p : pt) (e : edge) :
  valid_edge e p -> (p <<< e) = (p_y p < pvert_y p e).
Proof.
move=> val.
have xs : p_x p = p_x (Bpt (p_x p) (pvert_y p e)) by [].
have one : Bpt (p_x p) (pvert_y p e) === e by apply: pvert_on.
by rewrite (strict_under_edge_lower_y xs one).
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

Definition edge_side (evs : seq event) (open : seq cell) :=
  if evs is ev :: _ then
    all (fun g =>
        if valid_edge g (point ev) then
          if pvert_y (point ev) g <= p_y (point ev) then 
             p_x (point ev) < p_x (right_pt g)
          else
             p_x (left_pt g) < p_x (point ev)
        else
          true)
       [seq high c | c <- open]
  else true.

Lemma same_x_valid (p1 p2 : pt) (g : edge) :
  p_x p1 == p_x p2 -> valid_edge g p1 = valid_edge g p2.
Proof. by move=> /eqP xs; rewrite /valid_edge xs. Qed.

Lemma same_pvert_y (p1 p2 : pt) (g : edge) :
  valid_edge g p1 ->
  p_x p1 == p_x p2 -> pvert_y p1 g == pvert_y p2 g.
Proof.
move=> vg xs.
move: (vg) ; rewrite (same_x_valid _ xs) => vg2.
by have := on_edge_same_point (pvert_on vg) (pvert_on vg2) xs.
Qed.

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
move: adje; rewrite /= -[bottom]/(high extra_bot) adj_aux_path ocd.
rewrite ccdec -catA cat_path /= => /andP[] _.
by rewrite loc -[bottom]/(high extra_bot) last_map=> /andP[] /eqP.
Qed.

Lemma high_in_first_cells_below open p first_cells cc last_cells le he :
  open_cells_decomposition open p =
  (first_cells, cc, last_cells, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  seq_valid open p ->
  s_right_form open ->
  {in cell_edges open &, no_crossing} ->
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
have tr : {in [seq high i | i <- first_cells] & &, transitive edge_below}.
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

Lemma edge_below_pvert_y g1 g2 p :
  valid_edge g1 p -> valid_edge g2 p ->
  g1 <| g2 -> pvert_y p g1 <= pvert_y p g2.
Proof.
move=> v1 v2 g1g2.
have := pvert_on v1; set p' := Bpt _ _ => p'on.
have/esym := @same_x_valid p p' g1 (eqxx _); rewrite v1 => v'1.
have/esym := @same_x_valid p p' g2 (eqxx _); rewrite v2 => v'2.
have := order_edges_viz_point' v'1 v'2 g1g2.
rewrite (under_onVstrict v'1) p'on => /(_ isT).
by rewrite under_pvert_y //.
Qed.

(* To be added to math-comp. *)
Lemma sorted_catW (T : Type) (r : rel T) s s' :
 (sorted r (s ++ s')) -> sorted r s && sorted r s'.
Proof.
case: s => [// | a s] /=.
by rewrite cat_path => /andP[] ->; apply: path_sorted.
Qed.

Lemma edges_partition_strictly_above p g1 g2 s1 s2:
  all (valid_edge^~ p) (s1 ++ g1 :: g2 :: s2) ->
  sorted edge_below (s1 ++ g1 :: g2 :: s2) ->
  p >>= g1 -> p <<< g2 ->
  {in rcons s1 g1 &  g2 :: s2, forall g g', ~~ (g' <| g)}.
Proof.
move=> aval pth pg1 pg2.
have vg1 : valid_edge g1 p.
  by apply: (allP aval); rewrite !(mem_cat, inE) eqxx ?orbT.
have vg2 : valid_edge g2 p.
  by apply: (allP aval); rewrite !(mem_cat, inE) eqxx ?orbT.
have pg1y : pvert_y p g1 <= p_y p by rewrite leNgt -strict_under_pvert_y.
have pg2y : p_y p < pvert_y p g2 by rewrite -strict_under_pvert_y.
have g1g2 : pvert_y p g1 < pvert_y p g2 by apply: (le_lt_trans pg1y).
have mp : {in s1++ g1 :: g2 :: s2 &,
           {homo (pvert_y p) : x y / x <| y >-> x <= y}}.
    move=> u v /(allP aval) vu /(allP aval) vv uv.
    by apply: edge_below_pvert_y vu vv uv.
have sb2 : {subset [:: g1, g2 & s2] <= (s1 ++ [:: g1, g2 & s2])}.
  by move=> u uin; rewrite mem_cat uin orbT.
have g2s2y : {in g2 :: s2, forall g, pvert_y p g1 < pvert_y p g}.
  move=> g; rewrite inE => /orP[/eqP -> //| gin].
  have pthy : sorted <=%R [seq pvert_y p h | h <- g2 :: s2].
    apply: (homo_path_in mp); last first.
      move: pth.
      rewrite (_ : s1 ++ _ = (s1 ++[:: g1]) ++ g2 :: s2); last first.
        by rewrite /= -!catA.
      by move/sorted_catW=> /andP[].
    apply: (sub_all sb2).
    by apply/allP => z; rewrite !(mem_cat, inE) => /orP[] ->; rewrite ?orbT.
  have /(allP aval) gin' : g \in (s1 ++ [:: g1, g2 & s2]).
    by rewrite mem_cat !inE gin ?orbT.
  move: pthy; rewrite /= (path_sortedE le_trans) => /andP[] /allP.
  have giny : pvert_y p g \in [seq pvert_y p h | h <- s2] by apply: map_f.
  by move=> /(_ _ giny) => /(lt_le_trans g1g2).
have sb1 : {subset rcons s1 g1 <= s1 ++ [:: g1, g2 & s2]}.
  by move=> x; rewrite mem_rcons mem_cat !inE => /orP[] ->; rewrite ?orbT.
have s1g1y : {in rcons s1 g1, forall g, pvert_y p g <= pvert_y p g1}.
  move=> g; rewrite mem_rcons inE => /orP[/eqP ->| gin].
    apply: le_refl.
  case s1eq : s1 gin => [// | init s1']; rewrite -s1eq => gin.
  have pthy : sorted <=%R [seq pvert_y p h | h <- rcons s1 g1].
    rewrite s1eq /=; apply: (homo_path_in mp); last first.
      move: pth; rewrite s1eq/=.
      rewrite (_ : s1' ++ _ = (s1' ++ [:: g1]) ++ g2 :: s2); last first.
        by rewrite -catA.
      by rewrite cat_path cats1 => /andP[].
    by apply: (sub_all sb1); rewrite s1eq; apply: allss.
  have [s' [s'' s'eq]] : exists s' s'', s1 = s' ++ g :: s''.
    by move: gin=> /splitPr [s' s'']; exists s', s''.
  have dc : rcons (init :: s1') g1 = (s' ++ [:: g]) ++ rcons s'' g1.
   by rewrite -s1eq s'eq -!cats1 /= -?catA.
  case s'eq2 : s' => [ | init' s'2].
    move: pthy; rewrite s1eq dc s'eq2 /= (path_sortedE le_trans)=> /andP[].
    move=> /allP/(_ (pvert_y p g1)) + _; apply.
    by rewrite map_f // mem_rcons inE eqxx.
  move: pthy; rewrite s1eq dc s'eq2 /= map_cat cat_path => /andP[] _.
  rewrite !map_cat cats1 last_rcons (path_sortedE le_trans) => /andP[] + _.
  move=> /allP/(_ (pvert_y p g1)); apply.
  by apply: map_f; rewrite mem_rcons inE eqxx.
move=> g g' /[dup]gin /s1g1y giny /[dup] g'in /g2s2y g'iny; apply/negP=> g'g.
have vg : valid_edge g p by apply: (allP aval); apply: sb1.
have vg' : valid_edge g' p.
  by apply: (allP aval); apply: sb2; rewrite inE g'in orbT.
have:= edge_below_pvert_y vg' vg g'g; rewrite leNgt.
by rewrite (le_lt_trans _ g'iny).
Qed.

Lemma in_new_cell_not_in_first_old e open fc cc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  s_right_form open ->
  seq_valid open (point e) ->
  inside_box (point e) ->
  out_left_event e ->
  {in cell_edges open ++ outgoing e &, no_crossing} ->
  {in fc & opening_cells (point e) 
             (sort edge_below (outgoing e))
        le he, forall c1 c2, o_disjoint c1 c2}.
Proof.
move=> oe cbtom adj rfo sval inbox_e outs noc.
have ocd := decomposition_preserve_cells oe.
set result_open :=
   fc ++ opening_cells (point e) (sort edge_below (outgoing e)) le he ++ lc.
have steq : step e open nil = (result_open, closing_cells (point e) cc).
   by rewrite /step oe.
have adj' : adjacent_cells result_open.
  by have := step_keeps_adjacent inbox_e outs sval cbtom steq adj.
set new_cells := opening_cells _ _ _ _.
have := l_h_in_open cbtom adj inbox_e=> -[cle [che [clein [chein ]]]].
rewrite oe /= => -[leeq heeq].
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have [/eqP ole [/eqP ohe ccn0]]:=
   l_h_c_decomposition oe (exists_cell cbtom adj inbox_e).
have nceq : opening_cells (point e)
                  (sort edge_below (outgoing e)) le he = new_cells by [].
have [nle [nhe _]]:=
    higher_lower_equality outs oe nceq (exists_cell cbtom adj inbox_e)
         vle vhe.
have := open_not_nil (sort edge_below (outgoing e)) vle vhe.
rewrite -/new_cells => ncn0.
have [fceq | [fc' [lfc fceq]]] : fc = nil \/ exists fc' lfc, fc = rcons fc' lfc.
    by elim/last_ind : (fc) => [ | fc' lfc _];[left | right; exists fc', lfc].
  by rewrite fceq.
have lfceq : high lfc = le.
  case fc'eq : fc' => [ | init fc''].
    move: adj; rewrite ocd fceq fc'eq => /=.
    by move: ccn0 ole; case: (cc) => [ | b cc'] //= _ -> /andP[]/eqP ->.
  move: adj; rewrite ocd fceq fc'eq /= adj_aux_path cat_path=> /andP[] _.
  rewrite last_rcons.
  by move: ccn0 ole; case: (cc) => [ | b cc'] //= _ -> /andP[]/eqP ->.
set s1 := [seq high c | c <- fc'].
set s2 := [seq high c | c <- behead new_cells ++ lc].
set g2 := high (head dummy_cell new_cells).
have roeq : [seq high c | c <- result_open] = s1 ++ [:: le, g2 & s2].
  rewrite /result_open map_cat fceq -cats1 map_cat -catA /=.
  congr (_ ++ (_ :: _)) => //.
  rewrite /g2 /s2 2!map_cat -/new_cells.
  by move: ncn0; case: (new_cells).
have val' : all (valid_edge^~ (point e)) (s1 ++ [:: le, g2 & s2]).
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
  move: cin=>/opening_cells_subset=>/andP[] _.
  rewrite /= inE mem_sort=> /orP[/eqP -> //| /outs it].
  by apply: valid_edge_extremities; rewrite it.
have rfr' : sorted edge_below (s1 ++ [:: le, g2 & s2]).
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
have /andP[A B] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have p'under : p' <<< g2.
  have : head dummy_cell new_cells \in new_cells by rewrite head_in_not_nil.
  move=>/opening_cells_subset=> /andP[] _; rewrite -/g2 => g2in.
  rewrite (strict_under_pvert_y vg2').
  rewrite -(eqP (same_pvert_y vg2 samex)).
  apply: (lt_le_trans (_ : p_y p' < p_y (point e))).
    by rewrite [X in X < _]/= ltNge -(under_pvert_y vle).
  move: g2in; rewrite inE=> /orP[/eqP -> | ].
    by apply: ltW; rewrite -(strict_under_pvert_y vhe).
  rewrite mem_sort=>/outs/eqP lg2e.
  by rewrite -(under_pvert_y vg2) -lg2e left_pt_below.
have val'' : all (valid_edge^~ p') (s1 ++ [:: le, g2 & s2]).
  by apply/allP=> g gin; rewrite -(same_x_valid _ samex); apply: (allP val').
have := edges_partition_strictly_above val'' rfr' p'above p'under.
fail.

     

Lemma all_edges_opening_cells_above_first e open fc cc lc le he outg:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  s_right_form open ->
  seq_valid open (point e) ->
  inside_box (point e) ->
  {in cell_edges open ++ outg, forall g, inside_box (left_pt g)} ->
  {in cell_edges fc, forall g, p_x (point e) < p_x (right_pt g)} ->
  {in cell_edges open ++ outg &, no_crossing} ->
  {in outg, forall g, left_pt g == (point e)} ->
  {in cell_edges fc & 
      [seq high i | i <- (opening_cells (point e) outg le he)],
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
have noc' : {in cell_edges open &, no_crossing}.
  by move: noc; apply: sub_in2=> g gin; rewrite mem_cat gin.
rewrite (cell_edges_high fcn0 adjf) inE => /orP[/eqP -> | ].
  rewrite hdfc=> gin0.
  have gin : g2 \in outg ++ [:: he].
      move: gin0=>/mapP[c /opening_cells_subset /andP[] _ hiin geq].
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
  by move: (@valid_edge_extremities g (left_pt g)); rewrite eqxx; apply.
move=> /mapP[c2 /opening_cells_subset /andP[] _ g2in g2eq ].
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
have /andP[egtle elthe]:= l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have lelte: pvert_y (point e) le < p_y (point e).
  by move: egtle; rewrite (under_pvert_y vle) // -ltNge.
have eleg2 : p_y (point e) <= pvert_y (point e) g2.
  rewrite -(under_pvert_y v2).
  move: g2in; rewrite g2eq inE => /orP[ /eqP -> | /outs /eqP <-].
    by rewrite (under_onVstrict vhe) elthe orbT.
  by rewrite left_pt_below.
by apply: lt_le_trans eleg2.
Qed.

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


Lemma step_keeps_edge_side ev open closed open' closed' events :
  step ev open closed = (open', closed') ->
  inside_box (point ev) ->
  out_left_event ev ->
  s_right_form open ->
  cells_bottom_top open ->
  adjacent_cells open ->
  seq_valid open (point ev) ->
  close_edges_from_events (ev :: events) ->
  close_alive_edges open' events ->
  path lexPtEv ev events ->
  edge_side (ev :: events) open ->
  edge_side events open'.
Proof.
rewrite /step.
case oe: (open_cells_decomposition open (point ev)) => [[[[fc cc] lc] le] he].
have ocd := decomposition_preserve_cells oe.
move: events => [// | ev' events] [] <- _ {open' closed'}
  inbox_e outs rfo cbtom adj sval cle clae lexev /allP partedge.
apply/allP => g /mapP[c + geq]; rewrite !mem_cat => /orP[].
- move=> cfc.
  have fclow : c \in fc -> pvert_y (point ev) g <= p_y (point ev).
    admit.
  have : lexPtEv ev ev' by admit.
  move=> /orP[ xltx' | /andP[xs ys]]; move: (cfc)=> /fclow yev ; last first.
    case : ifP => // /[dup] ve'; rewrite -(same_x_valid _ xs) => ve.
    have := (ltW (le_lt_trans yev ys)); rewrite (eqP (same_pvert_y ve xs)).
    move=> ->; move: (partedge g); rewrite geq map_f; last first.
      by rewrite ocd !mem_cat cfc.
    by move=> /(_ isT); rewrite -geq ve yev (eqP xs).
  have := (allP clae c); rewrite !mem_cat cfc => /(_ isT).


case eveq : events => [ // | ev' events'].

move: (lexev); rewrite

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
  close_alive_edges open (ev :: events) ->
  all (fun x => lexPtEv ev x) events ->
  step ev open closed = (open', closed') ->
  {in open' &, disjoint_open_cells}.
Proof.
move=> cbtom adj inbox_e sval rfo /[dup] noc /inter_at_ext_no_crossing noc'
  disj outlefte cellsok clae lexev.
set ctxt := [seq low c | c <- open] ++ [seq high c | c <- open] ++ outgoing ev.
rewrite /step.
case oe: (open_cells_decomposition open (point ev)) => [[[[fc cc] lc] le] he].
have ocd := decomposition_preserve_cells oe.
have osub : {subset sort edge_below (outgoing ev) <= ctxt}.
  move=> g.
  have -> := perm_mem (permEl (perm_sort edge_below (outgoing ev))). 
  by move=> gin; rewrite /ctxt !mem_cat gin !orbT.
have := l_h_in_open cbtom adj inbox_e.
rewrite oe /= => -[cle [che [clein [chein [/esym cleq /esym cheq]]]]].
have /andP [eale euhe] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
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
                 [seq high c | c <- open] &, no_crossing}.
    by move: noc'; apply: sub_in2 => g gin; rewrite catA mem_cat gin.
  by have lowhigh := open_cells_decomposition_low_under_high 
                   noc2 cbtom adj inbox_e sval rfo oe.
have outlefts :
   {in sort edge_below (outgoing ev), forall g, left_pt g == point ev}.
  move=> g.
  have -> := perm_mem (permEl (perm_sort edge_below (outgoing ev))). 
  by apply: outlefte.
have noc2 : {in le :: he :: outgoing ev &, no_crossing}.
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
set fc_edges := [seq low c | c <- fc] ++ [seq high c | c <- fc].
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
  rewrite ocd -[bottom]/(high extra_bot) adj_aux_path cat_path last_rcons.
  by rewrite ccdec /= last_rcons lehcc => /andP[] _ /andP[] /eqP -> _. 
have lowvert : {in fc_edges, forall g, pvert_y (point ev) g < p_y (point ev)}.
  suff highs : {in [seq high c | c <- fc],
                 forall g, pvert_y (point ev) g < p_y (point ev)}.
    move=> g; rewrite mem_cat=>/orP[] gin; last by apply: highs.
    have fcn0 : fc != nil by move: gin; case: (fc).
    have : g \in rcons [seq low c| c <- fc] le.
      by rewrite mem_rcons inE gin orbT.
    have -> : le = high (last dummy_cell fc).
      move: adje; rewrite /= ocd -[bottom]/(high extra_bot) adj_aux_path.
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
    by rewrite /right_form edge_below_refl.
  rewrite /= => pathlt.
  move=> g /mapP[c cin gceq].
  have [s1 [s2 fceq]] : exists s1 s2, fc = s1 ++ c :: s2.
    by move: cin => /splitPr[ x y]; exists x, y.  
  have vertle : pvert_y (point ev) le < p_y (point ev).
    have := l_h_above_under_strict cbtom adj inbox_e sval rfo oe=> /andP[] + _.
    rewrite under_pvert_y; last first.
      rewrite lehcc ccdec; apply: (proj1 (andP (allP sval _ _))) => /=.
      by rewrite ocd ccdec !mem_cat /= inE eqxx ?orbT.
    by rewrite ltNge.
  elim/last_ind : (s2) fceq => [ | s2' ls2 _] fceq.
    rewrite gceq.
    move: adje; rewrite ocd fceq /= -[bottom]/(high extra_bot) adj_aux_path.
    rewrite cat_path ccdec /= cats1 last_rcons => /andP[] _ /andP[] /eqP higheq.
    by rewrite higheq -lehcc => _.
  move: pathlt; rewrite ocd fceq map_cat cat_path=> /andP[] + _.
  rewrite map_cat cat_path => /andP[] _ /= => /andP[] _.
  rewrite map_rcons path_sortedE; last by apply: le_trans.
  move=>/andP[] + _ => /allP /(_ (pvert_y (point ev) (high ls2))).
  rewrite mem_rcons inE eqxx -gceq => /(_ isT) first_part.
  apply: (le_lt_trans first_part) => {first_part}.
  move: (adje); rewrite /= -[bottom]/(high extra_bot) adj_aux_path.
  rewrite ocd fceq cat_path => /andP[] _.
  rewrite -[c :: _]/([:: c] ++ _) catA -rcons_cat last_rcons ccdec /=.
  by move=> /andP[]/eqP -> _; rewrite -lehcc.
have fcopen : {subset fc <= open}.
  by move=> g gin; rewrite ocd !mem_cat gin ?orbT.
have valfc : {in fc_edges, forall g, valid_edge g (point ev)}.
  by move=> g; rewrite /fc_edges mem_cat => /orP[]/mapP[c cin ->];
    case: (andP (allP sval c _))=> //; rewrite ocd !mem_cat cin ?orbT.
have edgesright: {in fc_edges, forall g, p_x (point ev) < p_x (right_pt g)}.
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
have noc3 : {in fc_edges &, no_crossing}.  
  move: noc'; apply: sub_in2 => g.
  by rewrite ocd !map_cat !mem_cat => /orP[] ->; rewrite ?orbT /=.
have tr : {in fc_edges & &, transitive edge_below}.
  by apply: (edge_below_trans _ valfc) => //; first by left; [].

have lowfc : {in fc_edges, forall g, g <| le}.
  suff highs : {in [seq high c | c <- fc], forall g, g <| le}.
    move=> g; rewrite mem_cat=>/orP[] gin; last by apply: highs.
    have fcn0 : fc != nil by move: gin; case: (fc).
    have : g \in rcons [seq low c| c <- fc] le.
      by rewrite mem_rcons inE gin orbT.
    have -> : le = high (last dummy_cell fc).
      move: adje; rewrite /= ocd -[bottom]/(high extra_bot) adj_aux_path.
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
    move: adje; rewrite /= -[bottom]/(high extra_bot) ocd fcteq fcteq' cats0 ccdec.
    rewrite cat_cons cats1 adj_aux_path cat_path => /andP[] _ /= => /andP[]/eqP + _.
    rewrite last_rcons geq -lehcc => ->; by rewrite edge_below_refl.
  move=> /andP[] /allP /(_ (high lf)) + _.
  rewrite -geq map_f; last by rewrite fcteq' mem_rcons inE eqxx.
  move=> /(_ isT) => ghlf.
  move: adje; rewrite /= -[bottom]/(high extra_bot) ocd fcteq fcteq' ccdec.
  rewrite cat_cons adj_aux_path cat_path => /andP[] _ /= => /andP[]/eqP + _.
  by rewrite last_cat last_rcons -lehcc => <-.
have ocdisjfc : {in oc & fc, forall c1 c2, o_disjoint c1 c2}.
  move=> c1 c2 c1in c2in p; apply/andP=> -[pino pinf].
  have := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  move=> /[dup] ib /andP[] ibl ibh.
  move: (pino) => /andP[] /[dup] invert /andP[] inverth invertl /valid_low_limits inhor.
  have nocs : {in [:: le, he & sort edge_below (outgoing ev)] &, no_crossing}.
    move: noc2; apply sub_in2=> x; rewrite !inE orbA=> /orP[ |].
     by move=> /orP[] /eqP ->; rewrite eqxx ?orbT.
    have -> := perm_mem (permEl (perm_sort edge_below (outgoing ev))). 
    by move=> ->; rewrite ?orbT.
  have := opening_cells_side_limit vle vhe lowhigh (underWC ibl) ibh nocs outlefts.
  move=> /allP ocoks.
  have := opening_cells_above_low lowhigh ib vle vhe _ outlefts nocs.
  have : {in sort edge_below (outgoing ev), forall g, left_pt g == point ev}.
    move: outlefts.
move=> [] <- _ => c1 c2.
rewrite !mem_cat !(orbCA (_ \in fc)).


suff main : {in predU (mem oc) (mem (fc ++ lc)) &, disjoint_open_cells}.
  by move=> inc1 inc2; apply: main; rewrite !(inE, mem_cat).
apply: add_new.
- exact: o_disjointC.
- by have := opening_cells_disjoint eale euhe lein hein lowhigh
              vle vhe osub noc' outlefts srt.
- move=> new old nin; rewrite mem_cat=>/orP[] oin p;
      apply/negP=>/andP[inew iold].
    have above : p >>> high old.
      have [fch [fct fcteq]] : exists fch fct, fc = fch ++ old :: fct.
        by move: oin => /splitPr [x y]; exists x, y.
      have oin2 : old \in old :: fct by rewrite inE eqxx.
      have rft : s_right_form (old :: fct) by admit.
      have adjt : adjacent_cells (old :: fct) by admit.
      have valt : {in low old::[seq high c | c <- old::fct],
                      forall g, valid_edge g (point ev)} by admit.
      have noct : {in low old::[seq high c | c <- old::fct] &,
                      no_crossing} by admit.
      have edge_cst : {in low old::[seq high c | c <- old::fct],
                   forall e, lexPt (point ev) (right_pt e)}.
        move=> g ; rewrite /= inE=> /orP[/eqP ->| gin ].
          have := (first_cells_right_pt clae inbox_e).
        have boxlex : forall g, g \in [:: bottom; top] ->
               lexPt (point ev) (right_pt g).
          move=> g lb.
          move: inbox_e => /andP[] _ /andP[] /andP[] _ t1 /andP[] _ t2.
          by move: lb; rewrite !inE /lexPt=>/orP[]/eqP ->; rewrite ?t1 ?t2.
        have claet : close_alive_edges (old :: fct) events by admit.
        move=> g gin.
        suff common : forall c, ((g == low c) || (g == high c)) ->
               c \in old :: fct -> lexPt (point ev) (right_pt g).
          by move: gin; rewrite /= !inE orbA => /orP[gin |/mapP[c cin gq]];
            [have:= (common old) | have:= (common c)];
            rewrite ?inE ?gin ?gq ?orbT ?cin ?eqxx; apply; rewrite ?orbT.
        move=> c gc cin; have := (allP claet _ cin)=>/andP[]; rewrite /end_edge.
        move=>/orP[]; first by apply: boxlex.
apply: common.
          move=> /orP[/orP[]/eqP -> | /mapP[c' c'i ->]];
            [have:= (common old) | have:= (common old) | have:= (common c')].

apply: common.
            apply: (common
            /orP[/eqP gq | ];[have:= common old | rewrite inE => /orP[/eqP gq | /mapP[c' c'in gq]]; [have := common old | have := common c' ]];
           rewrite !inE ?c'in ?gq ?eqxx ?orbT /=; apply.
           by rewrite !inE ?c'in ?gq ?eqxx ?orbT /=; apply.
           by rewrite !inE ?c'in ?gq ?eqxx ?orbT /=; apply.

/mapP[c cin gq]
; rewrite inE => /orP[/eqP -> | /mapP[ c' c'in geq]].
          have := (allP claet old oin2) => /andP[] +_ => /orP[lb | inevs].
            move: inbox_e => /andP[] _ /andP[] /andP[] _ t1 /andP[] _ t2.
            by move: lb; rewrite !inE /lexPt=>/orP[]/eqP ->; rewrite ?t1 ?t2.
          by move:inevs=>/hasP[ev' ev'in /eqP ->]; apply: (allP lexev).
                    
        have tr : {in mem (low old :: [seq high c | c <- old::fct]) & &,
                     transitive edge_below}.
          apply: (edge_below_trans _ valt) => //; left.
          by exact: edge_cst.
        admit.
(*
      have oldok : open_cell_side_limit_ok old.
        by apply: (allP cellsok); rewrite ocd !mem_cat oin.
      by move: iold=> /andP[] _ /(valid_high_limits oldok).
    move: iold=>/andP[]/andP[] + _ _; rewrite /point_strictly_under_edge.
    by rewrite ltNge le_eqVlt negb_or ltNge above andbF.
*)
    move: iold=>/andP[]/andP[] + _ _; rewrite /point_strictly_under_edge.
    by rewrite ltNge le_eqVlt negb_or ltNge above andbF.

  have abs : {in lc, forall c, valid_edge (low c) p -> p <<< low c}.
    admit.
  have below : p <<< low old.
    apply: abs=> //.
    have oldok : open_cell_side_limit_ok old.
      by apply: (allP cellsok); rewrite ocd !mem_cat oin !orbT.
    by move: iold=> /andP[] _ /(valid_low_limits oldok).
  move: iold=>/andP[]/andP[] _ + _; rewrite /point_strictly_under_edge.
  by rewrite -ltNge lt_neqAle leNgt [X in _ && ~~ X]below andbF.
move: disj; apply: sub_in2.
by rewrite ocd=> c; rewrite !mem_cat=> /orP[] ->; rewrite ?orbT.
Qed.

  
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
  - rewrite /open_limit /=.
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
