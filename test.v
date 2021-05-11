From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import cells.
Require Import trials.
Require Import draw.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Check two_triangles.

Definition tt_events := Eval compute in
      match trials.seq_nat_to_edges two_triangles with
      | Some v => edges_to_events v
      | _ => nil
      end.

Compute tt_events.

Check start.

Lemma scan_eq events open_cells closed_cells:
  scan events open_cells closed_cells =
      match events with 
      | [::] => closed_cells
      | e::q => let (open, closed) := (step e open_cells closed_cells) in  scan q open closed
 end.
Proof.  by case: events. Qed.





Compute (* map (fun c => display_cell "50 mul " c "") *) (start [::
     Bevent {| p_x := 1; p_y := 2 |} 
        [:: [edge of {| p_x := 1; p_y := 2 |},
                     {| p_x := 5; p_y := 1 |}];
            [edge of {| p_x := 1; p_y := 2 |},
                     {| p_x := 6; p_y := 17 |}]];
     Bevent {| p_x := 2; p_y := 2 |}
        
        [:: [edge of {| p_x := 2; p_y := 2 |},
                     {| p_x := 4; p_y := 4 |}];
            [edge of {| p_x := 2; p_y := 2 |},
                     {| p_x := 3; p_y := 5 |}]];
     Bevent {| p_x := 3%:R; p_y := 5%:R |}
        
        [:: [edge of {| p_x := 3%:R; p_y := 5%:R|},
                {| p_x := 4%:R; p_y := 4%:R|}]];
    Bevent {| p_x := 4%:R; p_y := 4%:R |}
           [::];
    Bevent {| p_x := 5%:R; p_y := 1%:R |}
      [:: [edge of {| p_x := 5; p_y := 1|},
                   {| p_x := 6; p_y := 17 |}]];
    Bevent {| p_x := 6; p_y := 17 |}
           [::]] dummy_low dummy_high).

Compute seq_nat_to_edges two_triangles.
Definition edge1 :=  Bedge
               (erefl
                  (p_x {| p_x := 2%:R; p_y := 2%:R |} <
                   p_x {| p_x := 4%:R; p_y := 4%:R |})).
Definition edge2 :=
   Bedge
               (erefl
                  (p_x {| p_x := 2%:R; p_y := 2%:R |} <
                   p_x {| p_x := 3%:R; p_y := 5%:R |})).
Definition edge3 := 
   Bedge
               (erefl
                  (p_x {| p_x :=1%:R; p_y := 2%:R |} <
                   p_x {| p_x := 5%:R; p_y := 1%:R |})).
Definition edge4 := 
   Bedge
               (erefl
                  (p_x {| p_x :=1%:R; p_y := 2%:R |} <
                   p_x {| p_x := 6%:R; p_y := 17%:R |})).
Arguments Bedge: clear implicits.
Definition ev0 :=
  {| point := {| p_x := 1%:R; p_y := 1%:R |};
     incoming := [::]; outgoing := [::] |}.

Definition ev1 : event := nth ev0 tt_events 0.
Definition ev2 : event := nth ev0 tt_events 1.
Definition ev3 : event := nth ev0 tt_events 2.
Definition ev4 : event := nth ev0 tt_events 3.
Definition ev5 : event := nth ev0 tt_events 4.
Definition ev6 : event := nth ev0 tt_events 5.
Definition ev7 : event := nth ev0 tt_events 6.
(* example of step-by-step execution. *)
(*
Lemma sandbox : start tt_events dummy_low dummy_high = nil.
rewrite /start.
rewrite /tt_events.
set e := outgoing _.
compute in e.
rewrite /e.
set es := (X in scan X).

set c1 := (init_cells _ _ _).
rewrite scan_eq.
rewrite /es.
set Vs := (step _ _ _).
compute in Vs.
rewrite /Vs.
rewrite scan_eq.
rewrite /es.
set Vs2 := (step _ _ _).
compute in Vs2.
Admitted.


Lemma sandbox2 : step ev2 (init_cells
        (point ev1) (head edge1 (outgoing ev1)) (behead (outgoing ev1))) [::]  = (nil,nil).
Proof.
rewrite /init_cells /=.
rewrite /step.
set V:= extract_l_h_edges _.
compute in V.
compute.
move => e0 rest.
case nn: (step e0 c1 [::]) => [open closed].
compute in nn.
Admitted.

*)