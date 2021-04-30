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
Notation "[ 'rat' 'of' 'int' x ]" := (Rat (fracq_subproof (Posz x, Posz 1))).

Notation "[ 'rat' 'of' x , y ]" :=  (Rat (fracq_subproof (x, y))).

(* En entrée, les rationnels qui sont en fait des entiers positifs peuvent
  aussi s'écrire 2%:R, etc. *)

Definition rat_of_nat (x : nat) : rat :=  x%:R.

Coercion rat_of_nat : nat >-> rat.

Definition mk_edge (a b c d : nat) : option edge :=
  let a' := a%:R in
  let b' := b%:R in
  let c' := c%:R in
  let d' := d%:R in
  match (a' < c') as x return (a' < c') = x -> option edge with
  | true => fun h =>
     Some (@Bedge {| p_x := a'; p_y := b'|} {| p_x := c'; p_y := d'|} h)
  | false => fun _ => None
  end erefl.

Fixpoint seq_nat_to_edges (s : seq nat) : option (seq edge) :=
  match s with
  | nil => Some nil
  | a :: b :: c :: d :: tl =>
    match mk_edge a b c d with
    | Some e =>
       match seq_nat_to_edges tl with Some r => Some (e :: r) | _ => None end
    | _ => None
    end
  | _ => None
  end.

Definition dummy_low := @Bedge (Bpt 0%:Q 0%:Q) (Bpt 50%:Q 0%:Q) isT.

Definition dummy_high := @Bedge (Bpt 0%:Q 50%:Q) (Bpt 50%:Q 50%:Q) isT.

Definition test (s : seq nat) : option (seq cell) :=
  match seq_nat_to_edges s with
  | Some v => Some (start (edges_to_events v) dummy_low dummy_high )
  | _ => None
  end.

Definition newline := 
  String (Ascii.Ascii false true false true false false false false)
        EmptyString.

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

Definition rat_to_string (scale : string) (r : rat) (buffer : string) :=
  let v := valq r in
  if (v.2 == 1) then
    int_to_string v.1 (concat "" [:: " "; scale; " "; buffer]%string)
  else
     int_to_string v.1 (concat "" [:: " "; scale; " ";
       (int_to_string v.2 (concat "" [:: " div "; buffer]))]%string).

Definition cats (s1 s2: string) := concat "" [:: s1; s2].

Definition display_segment (scale : string)
   (p1 p2 : pt) (buffer : string) : string :=
  rat_to_string scale (p_x p1) (rat_to_string scale (p_y p1)
    (cats "moveto "
      (rat_to_string scale (p_x p2) (rat_to_string scale (p_y p2)
         (concat "" ([:: "lineto"; newline; buffer])%string))))).

Fixpoint iterate_cell_border (scale : string) (f : string -> pt -> pt -> string -> string)
  (last : pt) (s : seq pt) (buffer : string) :=
  match s with
  | nil => buffer
  | p :: nil => f scale p last buffer
  | p1 :: (p2 :: _) as tl =>
    let buffer' := iterate_cell_border scale f last tl buffer in
    f scale p1 p2 buffer'
  end.

Definition display_cell_border scale s buffer :=
  match s with
  | a :: tl => iterate_cell_border scale display_segment a s buffer
  | nil => buffer
  end.

Definition display_cell scale (c : cell) (buf : string) : string :=
  display_cell_border scale (pts c) buf.

Definition dtest (s : seq nat) :=
  match test s with
  | Some v =>
    concat newline ([:: ""; "%!PS"; "100 100 translate"; "newpath";
    foldr (display_cell (cats 
    newline    
    "20 mul "%string)) 
    (concat newline [:: "stroke"; "showpage"; "EOF"; ""]) v])%string
  | None => EmptyString
  end.
