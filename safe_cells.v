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

Hypothesis closed_ok : {in closed, forall c, closed_cell_side_limit_ok c}.
Hypothesis noc : {in obstacles &, forall g1 g2, inter_at_ext g1 g2}.

Lemma above_low : {in closed, forall c p, p === high c -> p >>= low c}.
Admitted.

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
have {}lpcc : left_limit pc1 <= p_x p.
  by move:(pong)=> /andP[] _ /andP[]; rewrite lpcc.
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
