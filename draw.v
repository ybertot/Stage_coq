From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import cells.
Require Import trials.

Definition one_triangle : seq nat :=
  [:: 2; 2; 4; 4; 2; 2; 3; 5; 3; 5; 4; 4].

Definition two_triangles : seq nat :=
  [:: 1; 2; 5; 1; 1; 2; 6; 17; 5; 1; 6; 17] ++ one_triangle.

(* To exploit this computation and produce a postscript file, you should
just type the following command on a unix system, where draw.v is the name
of this file

  coqc draw.v 2>/dev/null | tail -n +2 | head -n -3 > example.ps

You can then display example.ps with a postscript viewer or convert it to
other formats. *)
Compute dtest two_triangles.
