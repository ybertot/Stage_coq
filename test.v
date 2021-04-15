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


(* example of step-by-step execution. *)
Lemma sandbox : start tt_events = nil.
rewrite /start.
rewrite /tt_events.
set e := outgoing _.
compute in e.
rewrite /e.
set es := (X in scan X).
set c1 := (init_cells _ _ _).
rewrite scan_eq.
