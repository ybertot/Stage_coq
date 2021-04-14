From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import cells.
Require Import trials.

Definition one_triangle : seq nat :=
  [:: 2; 2; 4; 4; 2; 2; 3; 5; 3; 5; 4; 4].

Definition two_triangles : seq nat :=
  [:: 1; 2; 5; 1; 1; 2; 6; 17; 5; 1; 6; 17] ++ one_triangle.

Compute dtest two_triangles.
