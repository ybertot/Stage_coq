From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import cells.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

(* Une notation plus jolie pour les arêtes. *)
Notation "[ 'edge' 'of' p1 , p2 ]" := (@Bedge p1 p2 is_true_true)
  (at level 0, format  "[ 'edge'  'of'  p1 ','  p2 ]").


(* Une notation pour les nombres rationnels qui sont en fait des entiers. *)
Notation "[ 'rat' 'of' 'int' x ]" := (Rat (fracq_subproof (x, Posz 1))).

(* En entrée, les rationnels qui sont en fait des entiers positifs peuvent
  aussi s'écrire 2%:R, etc. *)

(* Un essai de la fonction scan sur un triangle. *)
Compute scan [:: 
     Bevent {| p_x := 2%:R; p_y := 4%:R |}
        [:: [edge of {| p_x := 1; p_y := 1%:R |},
                {| p_x := 2%:R; p_y := 4%:R|}]]
        [:: [edge of {| p_x := 2%:R; p_y := 4%:R|},
                {| p_x := 3%:R; p_y := 3%:R|}]];
    Bevent {| p_x := 3%:R; p_y := 3%:R |}
      [:: [edge of {| p_x := 1%:R; p_y := 1%:R |},
              {| p_x := 3%:R; p_y := 3%:R |}];
          [edge of {| p_x := 2%:R; p_y := 4%:R |},
              {| p_x := 3%:R; p_y := 3%:R |}]] [::] ]
   [:: {| pts := [:: {| p_x := 1; p_y := 1|}];
          low := [edge of {| p_x := 1%:R; p_y := 1%:R |},
              {| p_x := 3%:R; p_y := 3%:R |}];
          high := [edge of {| p_x := 1; p_y := 1%:R |},
                {| p_x := 2%:R; p_y := 4%:R|}] |} ] [::].
