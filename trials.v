From mathcomp Require Import all_ssreflect all_algebra.
Require Import String.
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

Notation "[ 'rat' 'of' x , y ]" :=  (Rat (fracq_subproof (x, y))).

(* En entrée, les rationnels qui sont en fait des entiers positifs peuvent
  aussi s'écrire 2%:R, etc. *)

Definition rat_of_nat (x : nat) : rat :=  x%:R.

Coercion rat_of_nat : nat >-> rat.

(* Un essai de la fonction scan sur un triangle. *)

Definition digits := "0123456789"%string.

Fixpoint nat_to_st (fuel : nat) (n : nat) (buffer : string) :=
  match fuel with
  | S p =>
    let d := (n %% 10)%N in
    let n' := (n %/ 10)%N in
    let buffer' := match get d digits with
    | Some da => String da buffer
    | None => buffer
    end in
    if n' == 0%N then buffer' else nat_to_st p n' buffer'
  | 0 => concat ""%string [:: "0"%string; buffer]
  end.

Definition nat_to_string (n : nat) (buf : string) :=
  nat_to_st n n buf.

Definition int_to_string (n : int) (buf : string) :=
  match n with
  | Posz n => nat_to_string n buf
  | Negz n => nat_to_string n.+1 (concat "" [:: " opp "; buf]%string)
  end.

Compute (int_to_string (-(2%:R))) "".

Definition rat_to_string (scale : string) (r : rat) (buffer : string) :=
  let v := valq r in
  if (v.2 == 1) then
    int_to_string v.1 (concat "" [:: " "; scale; " "; buffer]%string)
  else
     int_to_string v.1 (concat "" [:: " "; scale; " ";
       (int_to_string v.2 (concat "" [:: " div "; buffer]))]%string).

Compute rat_to_string "100 mul" 5 "".

Definition cats (s1 s2: string) := concat "" [:: s1; s2].

Definition display_segment (scale : string)
   (p1 p2 : pt) (buffer : string) : string :=
  rat_to_string scale (p_x p1) (rat_to_string scale (p_y p1)
    (cats "moveto "
      (rat_to_string scale (p_x p2) (rat_to_string scale (p_y p2)
         (cats "lineto " buffer))))).

Fixpoint iterate_cell_border (scale : string) (f : string -> pt -> pt -> string -> string)
  (last : pt) (s : seq pt) (buffer : string) :=
  match s with
  | nil => buffer
  | p :: nil => f scale p last buffer
  | p1 :: (p2 :: _ as tl) =>
    let buffer' := iterate_cell_border scale f last tl buffer in
    f scale p1 p2 buffer'
  end.

Definition display_cell_border scale s buffer :=
  match s with
  | a :: tl => iterate_cell_border scale display_segment a tl buffer
  | nil => buffer
  end.

Definition display_cell scale (c : cell) (buf : string) : string :=
  display_cell_border scale (pts c) buf.

Compute (* map (fun c => display_cell "50 mul " c "") *) (start [::
     Bevent {| p_x := 2; p_y := 2 |}
        [::]
        [:: [edge of {| p_x := 2; p_y := 2 |},
                     {| p_x := 4; p_y := 4 |}];
            [edge of {| p_x := 2; p_y := 2 |},
                     {| p_x := 3; p_y := 5 |}]];
     Bevent {| p_x := 3%:R; p_y := 5%:R |}
        [:: [edge of {| p_x := 2; p_y := 2%:R |},
                {| p_x := 3%:R; p_y := 5%:R|}]]
        [:: [edge of {| p_x := 3%:R; p_y := 5%:R|},
                {| p_x := 4%:R; p_y := 4%:R|}]];
    Bevent {| p_x := 4%:R; p_y := 4%:R |}
      [:: [edge of {| p_x := 2%:R; p_y := 2%:R |},
              {| p_x := 4%:R; p_y := 4%:R |}];
          [edge of {| p_x := 3%:R; p_y := 5%:R |},
              {| p_x := 4%:R; p_y := 4%:R |}]] [::]]).



Compute (* map (fun c => display_cell "50 mul " c "") *) (start [::
     Bevent {| p_x := 1; p_y := 2 |} [::]
        [:: [edge of {| p_x := 1; p_y := 2 |},
                     {| p_x := 5; p_y := 1 |}];
            [edge of {| p_x := 1; p_y := 2 |},
                     {| p_x := 6; p_y := 17 |}]];
     Bevent {| p_x := 2; p_y := 2 |}
        [::]
        [:: [edge of {| p_x := 2; p_y := 2 |},
                     {| p_x := 4; p_y := 4 |}];
            [edge of {| p_x := 2; p_y := 2 |},
                     {| p_x := 3; p_y := 5 |}]];
     Bevent {| p_x := 3%:R; p_y := 5%:R |}
        [:: [edge of {| p_x := 2; p_y := 2%:R |},
                {| p_x := 3%:R; p_y := 5%:R|}]]
        [:: [edge of {| p_x := 3%:R; p_y := 5%:R|},
                {| p_x := 4%:R; p_y := 4%:R|}]];
    Bevent {| p_x := 4%:R; p_y := 4%:R |}
      [:: [edge of {| p_x := 2%:R; p_y := 2%:R |},
              {| p_x := 4%:R; p_y := 4%:R |}];
          [edge of {| p_x := 3%:R; p_y := 5%:R |},
              {| p_x := 4%:R; p_y := 4%:R |}]] [::];
    Bevent {| p_x := 5%:R; p_y := 1%:R |}
      [:: [edge of {| p_x := 1%:R; p_y := 2%:R|},
                   {| p_x := 5%:R; p_y := 1|}]]
      [:: [edge of {| p_x := 5; p_y := 1|},
                   {| p_x := 6; p_y := 17 |}]];
    Bevent {| p_x := 6; p_y := 17 |}
      [:: [edge of {| p_x := 5; p_y := 1|},
              {| p_x := 6; p_y := 17 |}];
          [edge of {| p_x := 1; p_y := 2|},
             {|p_x := 6; p_y := 17 |}]] [::]]).

Compute map pts (start [::
     Bevent {| p_x := 1; p_y := 2 |} [::]
        [:: [edge of {| p_x := 1; p_y := 2 |},
                     {| p_x := 5; p_y := 1 |}];
            [edge of {| p_x := 1; p_y := 2 |},
                     {| p_x := 6; p_y := 17 |}]];
     Bevent {| p_x := 2; p_y := 2 |}
        [::]
        [:: [edge of {| p_x := 2; p_y := 2 |},
                     {| p_x := 4; p_y := 4 |}];
            [edge of {| p_x := 2; p_y := 2 |},
                     {| p_x := 3; p_y := 5 |}]];
     Bevent {| p_x := 3%:R; p_y := 5%:R |}
        [:: [edge of {| p_x := 2; p_y := 2%:R |},
                {| p_x := 3%:R; p_y := 5%:R|}]]
        [:: [edge of {| p_x := 3%:R; p_y := 5%:R|},
                {| p_x := 4%:R; p_y := 4%:R|}]];
    Bevent {| p_x := 4%:R; p_y := 4%:R |}
      [:: [edge of {| p_x := 2%:R; p_y := 2%:R |},
              {| p_x := 4%:R; p_y := 4%:R |}];
          [edge of {| p_x := 3%:R; p_y := 5%:R |},
              {| p_x := 4%:R; p_y := 4%:R |}]] [::];
    Bevent {| p_x := 5%:R; p_y := 1%:R |}
      [:: [edge of {| p_x := 1%:R; p_y := 2%:R|},
                   {| p_x := 5%:R; p_y := 1|}]]
      [:: [edge of {| p_x := 5; p_y := 1|},
                   {| p_x := 6; p_y := 17 |}]];
    Bevent {| p_x := 6; p_y := 17 |}
      [:: [edge of {| p_x := 5; p_y := 1|},
              {| p_x := 6; p_y := 17 |}];
          [edge of {| p_x := 1; p_y := 2|},
             {|p_x := 6; p_y := 17 |}]] [::]]).

Compute vertical_intersection_point {| p_x := 3; p_y := 5|}
     [edge of {| p_x := 1; p_y := 2 |},
                     {| p_x := 6; p_y := 17 |}].

Compute pue_formula  {| p_x := 1; p_y := 2|}  {| p_x := 3; p_y := 5|}
     {| p_x := 6; p_y := 7|}.
