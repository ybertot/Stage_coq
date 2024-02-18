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

Variables closed open : seq cell.
Variables bottom top : cell.
Variable obstacles : seq edge.
Variables points : seq pt.

Hypothesis obstacles_in :
  {subset [seq left_pt g | g <- obstacles] ++ [seq right_pt g | g <- obstacles]
     <= points}.

Hypothesis disj_closed :  {in closed &, disjoint_closed_cells R}.
Hypothesis disj_open :  {in open & closed, disjoint_open_closed_cells R}.
Hypothesis coverage : {in obstacles, forall g, edge_covered g open closed}.
Hypothesis covered_points :
   {in points, forall p, exists2 c, c \in open ++ closed & p \in left_pts c}.
