From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import math_comp_complements points_and_edges events cells.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section working_environment.

Variable R : realFieldType.

Notation pt := (pt R).
Notation edge := (edge R).
Notation event := (event R).

Notation cell := (cell R).

Notation dummy_pt := (dummy_pt R).
Notation dummy_edge := (dummy_edge R).
Notation dummy_cell := (dummy_cell R).

(* this function removes consecutives duplicates, meaning the seq needs
 to be sorted first if we want to remove all duplicates *)
Fixpoint no_dup_seq (A : eqType) (s : seq A) : (seq A) :=
  match s with
  | [::] => [::]
  | a::q => match q with
            | [::] => s
            | b::r => if a == b then no_dup_seq q else a::(no_dup_seq q)
            end
    end.

Definition close_cell (p : pt) (c : cell) :=
  match vertical_intersection_point p (low c),
        vertical_intersection_point p (high c) with
  | None, _ | _, None => c
  | Some p1, Some p2 => 
    Bcell (left_pts c) (no_dup_seq [:: p1; p; p2]) (low c) (high c)
  end.

Definition closing_cells (p : pt) (contact_cells: seq cell) : seq cell :=
  [seq close_cell p c | c <- contact_cells].

Lemma close_cell_preserve_3sides p c :
  [/\ low (close_cell p c) = low c,
      high (close_cell p c) = high c &
      left_pts (close_cell p c) = left_pts c].
Proof.
rewrite /close_cell.
case: (vertical_intersection_point p (low c))=> [p1 | ] //.
by case: (vertical_intersection_point p (high c))=> [p2 | ].
Qed.

(* at each step we create the cell under the first outgoing edge and when there's only one left,
we create the two last cells *)
Fixpoint opening_cells_aux (p : pt) (out : seq edge) (low_e high_e : edge) 
  : seq cell * cell :=
      match out with
    | [::] => let op0 := vertical_intersection_point p low_e in
              let op1 := vertical_intersection_point p high_e in
                      match (op0,op1) with
                          |(None,_) |(_,None)=> ([::], dummy_cell)
                          |(Some(p0),Some(p1)) =>
                              ([::] , Bcell  (no_dup_seq ([:: p1; p; p0])) [::] low_e high_e)                      end
    | c::q => let op0 := vertical_intersection_point p low_e in
              let (s, nc) := opening_cells_aux p q c high_e in
                    match op0 with
                       | None => ([::], dummy_cell)
                       | Some(p0) =>
                        (Bcell  (no_dup_seq([:: p; p0])) [::] low_e c :: s,
                         nc)
                    end
end.

Definition opening_cells (p : pt) (out : seq edge) (l h : edge) : seq cell :=
   let (s, c) := opening_cells_aux p (sort (@edge_below R) out) l h in
   rcons s c.

Lemma opening_cells_left p out le he :
  {in out, forall g, left_pt g == p} ->
  valid_edge le p ->
  valid_edge he p ->
  {in opening_cells p out le he, forall c, left_limit c = p_x p}.
Proof.
move=> outl vle vhe; rewrite /opening_cells.
have : forall g, g \in sort (@edge_below _) out -> left_pt g == p.
  by move=> g; rewrite mem_sort; apply outl.
elim: (sort _ _) le vle => [ | g1 gs Ih] le vle {}outl c.
  rewrite /= pvertE // pvertE //=.
  by case: ifP=> _; case: ifP=> _; rewrite inE /left_limit => /eqP ->.
have outl' : forall g, g \in gs -> left_pt g == p.
  by move=> g gin; apply outl; rewrite inE gin orbT.
rewrite /=.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (outl g1 _)) ?valid_edge_left // inE eqxx.
move: Ih; case oca_eq : (opening_cells_aux _ _ _ _) => [s c'] /(_ _ vg1 outl').
rewrite oca_eq => Ih.
rewrite pvertE //=.
rewrite inE => /orP[/eqP -> | ]; first by rewrite /left_limit; case : ifP.
by apply: Ih.
Qed.

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

Definition step (e : event) (open_cells : seq cell) (closed_cells : seq cell) : (seq cell) * (seq cell) :=
   let p := point e in
   let '(first_cells, contact_cells, last_cells, lower_edge, higher_edge) := open_cells_decomposition open_cells p in
   let closed := closing_cells p contact_cells in
   let closed_cells := closed_cells++closed in
   let new_open_cells :=
     opening_cells p (outgoing e) lower_edge higher_edge in
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

Definition start_open_cell (bottom top : edge) :=
  Bcell (leftmost_points bottom top) [::] bottom top.

Definition start (events : seq event) (bottom : edge) (top : edge) :
  seq cell * seq cell :=
  scan events [:: start_open_cell bottom top] [::].

Section proof_environment.
Variables bottom top : edge.

Notation extra_bot := (extra_bot bottom).
Notation end_edge := (end_edge bottom top).
Notation close_out_from_event := (close_out_from_event bottom top).
Notation close_edges_from_events :=
  (close_edges_from_events bottom top).
Notation close_alive_edges := (close_alive_edges bottom top).
Notation cells_bottom_top := (cells_bottom_top bottom top).
Notation inside_box := (inside_box bottom top).
Notation open_cell_side_limit_ok := (@open_cell_side_limit_ok R).
Notation seq_low_high_shift := (@seq_low_high_shift R).
Notation cover_left_of := (@cover_left_of _ bottom top).

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
(exists2 c, c \in open_cells & contains_point' pt c) ->
(low (head dummy_cell contact) == low_f) /\ (high (last dummy_cell contact) == high_f) /\ contact != nil.
Proof.
  move => f_c c_c l_c lowf highf.
rewrite /=.
elim : open_cells fc => [/= | c q IH] fc.
  move =>   _ /= [] x.
   rewrite in_nil=> //.
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
move : exi => [] x xin /[dup] xcontains /contains_point'W xcontainsw.
rewrite inE in xin .
move : xin => /orP [ /eqP xeqp | xinq2].
  rewrite -xeqp in notcontain.
  by rewrite notcontain in xcontainsw.
by exists x.
Qed.

Lemma l_h_c_decomposition open_cells pt :
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition open_cells pt  = (first_cells, contact, last_cells, low_f, high_f)   ->
(exists2 c, c \in open_cells & contains_point' pt c) ->
(low (head dummy_cell contact) == low_f) /\ (high (last dummy_cell contact) == high_f) /\ contact != nil .
Proof.
rewrite /=.
case :  open_cells  => [/= | c q] fc c_c lc low_f high_f.
move => [] _ <- _ _ _ []x.
rewrite in_nil => //.
rewrite /open_cells_decomposition.
move => h.
by have  := (l_h_c_fix h).
Qed.

Lemma opening_cells_seq_edge_shift p s c oe le he :
  {in oe, forall g, left_pt g == p} ->
  valid_edge le p -> valid_edge he p ->
  opening_cells_aux p oe le he = (s, c) ->
  le :: [seq high i | i <- rcons s c] =
  rcons [seq low i | i <- rcons s c] he.
Proof.
move=> + + vh.
elim: oe le s c => [ | g1 oe Ih] le s c leftg vl /=.
  by rewrite pvertE // pvertE // => -[] <- <- /=.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (leftg g1 _)) ?valid_edge_left // inE eqxx.
have leftg' : {in oe, forall g, left_pt g == p}.
  by move=> g gin; apply: leftg; rewrite inE gin orbT.
have := Ih _ _ _ leftg' vg1; case: (opening_cells_aux _ _ _ _)=> [s' c'].
move=> /(_ s' c' erefl) {}Ih.
by rewrite pvertE // => -  [] <- <- /=; congr (_ :: _).
Qed.

Lemma opening_cells_aux_subset c' s' c p s le he:
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  opening_cells_aux p s le he = (s', c') ->
  c \in rcons s' c' ->
  (low c \in le :: s) && (high c \in he :: s).
Proof.
move=> + vhe.
elim: s c' s' le => [ | g1 s Ih] c' s' le /= vle lsp.
rewrite pvertE // pvertE // => - [] <- <-.
by do 2 (case: ifP=> _); rewrite /= inE=> /eqP -> /=;
  rewrite !inE !eqxx.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (lsp g1 _)) ?valid_edge_left // inE eqxx.
have lsp' : {in s, forall g, left_pt g == p}.
  by move=> g gin; rewrite lsp // inE gin orbT.
have := Ih _ _ _ vg1 lsp'; case: (opening_cells_aux _ _ _ _)=> [s1 c1].
move=> /(_ _ _ erefl) {} Ih.
rewrite pvertE // => - [] <- <- /=; rewrite inE=> /orP[/eqP -> /= | ].
  by rewrite !inE ?eqxx ?orbT.
rewrite inE; move=>/Ih/andP[] ->; rewrite orbT andTb.
by rewrite !inE orbCA => ->; rewrite orbT.
Qed.


Lemma opening_cells_subset c p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  c \in opening_cells p s le he ->
  (low c \in le :: s) && (high c \in he :: s).
Proof.
move=> vle vhe cin.

(*
move=> cin.
have:= opening_cells_aux_subset cin.
by rewrite !inE !(perm_mem (permEl (perm_sort _ _))).
Qed.
*)
Admitted.

(*
Lemma opening_cells_aux_nnil p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  opening_cells_aux p s le he != nil.
Proof.
by move=> + vhe; case: s => [ | g1 s] vle lsp; rewrite /= pvertE // ?pvertE.
Qed.
*)

Lemma opening_cells_aux_high p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  [seq high i | i <- (opening_cells_aux p s le he).1] = s.
Proof.
move=> vle vhe lsp.
elim: s le vle lsp => [ | g1 s Ih] le vle lsp.
  by rewrite /= pvertE // pvertE.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (lsp g1 _)) ?valid_edge_left // inE eqxx.
have lsp' : {in s, forall g, left_pt g == p}.
  by move=> g gin; apply: lsp; rewrite inE gin orbT.
rewrite /= pvertE //.
by have := Ih _ vg1 lsp'; case: (opening_cells_aux _ _ _ _) => [s' c'] /= ->.
Qed.

Lemma opening_cells_aux_high_last p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  high (opening_cells_aux p s le he ).2 = he.
Proof.
move=> + vhe; elim: s le => [ /= | g1 s Ih] le vle lsp.
  by rewrite pvertE // pvertE.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (lsp g1 _)) ?valid_edge_left // inE eqxx.
have lsp' : {in s, forall g, left_pt g == p}.
  by move=> g gin; apply: lsp; rewrite inE gin orbT.
have := Ih _ vg1 lsp'; rewrite /= pvertE //.
by case : (opening_cells_aux _ _ _ _) => [s' c'].
Qed.

Lemma opening_cells_high p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  [seq high i | i <- opening_cells p s le he] =
  rcons (sort (@edge_below R) s) he.
Proof.
move=> vle vhe lsp; rewrite /opening_cells.
have lsp' :
   {in sort (@edge_below _) s, forall g, left_pt g == p}.
  move=> g; rewrite mem_sort; apply: lsp.
move: (lsp') => /opening_cells_aux_high => /(_ _ _ vle vhe).
move: lsp' => /opening_cells_aux_high_last => /(_ _ _ vle vhe).
case: (opening_cells_aux _ _ _ _) => [s' c'] /=.
by rewrite map_rcons => -> ->.
Qed.

Lemma opening_cells_aux_right_form (ctxt s : seq edge) (p : pt) le he
 s' c' :
p >>= le -> p <<< he -> valid_edge le p -> valid_edge he p ->
le \in ctxt -> he \in ctxt ->
le <| he -> {in s, forall g, left_pt g == p} ->
{in ctxt &, (@no_crossing R)} ->
{subset s <= ctxt} ->
path (@edge_below R) le s  ->
opening_cells_aux p s le he = (s', c') ->
s_right_form (rcons s' c').
Proof.
move=> + ph + vh + hin + + noc + +.
elim: s le s' c' => [ | g1 edges IH] le s' c'
  pabove vle lin lowhigh outs allin sorted_e /=.
  by rewrite pvertE // pvertE // => -[] <- <- /=; rewrite andbT.
rewrite pvertE //.
have outs' : {in edges, forall g, left_pt g == p}.
  by move=> g gin; apply outs; rewrite inE gin orbT.
have allin' : {subset edges <= ctxt}.
  by move=> g gin; rewrite allin // inE gin orbT.
have sorted_e' : path (@edge_below R) g1 edges.
   by apply: (path_sorted sorted_e).
have /eqP gl : left_pt g1 == p by rewrite outs // inE eqxx.
have g1belowhigh : g1 <| he.
  have gin' : g1 \in ctxt by rewrite allin // inE eqxx.
  have/no_crossingE := noc g1 he gin' hin.
  by rewrite gl=>/(_ vh)=> -[]/(_ ph).
have pong : p === g1 by rewrite -gl left_on_edge.
have paboveg1 : p >>= g1
   by rewrite strict_nonAunder ?pong //; case/andP: pong.
move: (sorted_e) => /=/andP[] leg1 _.
have g1in : g1 \in ctxt by rewrite allin // inE eqxx.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (outs g1 _)) ?valid_edge_left // inE eqxx.
have := IH g1 _ _ paboveg1 vg1 g1in g1belowhigh outs' allin' sorted_e'.
case: (opening_cells_aux _ _ _ _) => [s1 c1] - /(_ _ _ erefl) {} IH /=.
by move=> [] <- <- /=; rewrite leg1.
Qed.

Lemma opening_cells_right_form p s low_e high_e :
valid_edge low_e p ->
valid_edge high_e p ->
p >>= low_e -> p <<< high_e ->
low_e <| high_e ->
{in s, forall g, left_pt g == p} ->
{in s, forall g, low_e <| g} ->
{in s, forall g, g <| high_e} ->
{in s &, (@no_crossing R)} ->
s_right_form (opening_cells p s low_e high_e).
Proof.
set mainsort := fun l => (perm_mem (permEl (perm_sort (@edge_below R) l))).
move=> vl vh pabove punder lowhigh outs alla allb noc; apply/allP.
have noc' : {in low_e :: high_e :: s &, (@no_crossing R)}.
  move=> e1 e2; rewrite !inE !orbA =>/orP[e1lh |e1in ]/orP[e2lh |e2in].
    by apply/orP;move:e1lh e2lh=> /orP[]/eqP -> /orP[]/eqP ->;
      rewrite ?edge_below_refl ?lowhigh ?orbT.
    - by move: e1lh=> /orP[]/eqP ->;apply/orP;
         rewrite/below_alt ?alla ?allb ?orbT.
    - by move: e2lh=> /orP[]/eqP ->; apply/orP;
         rewrite/below_alt ?alla ?allb ?orbT.
    by apply: noc.
have sorted_e : sorted (@edge_below R) (sort (@edge_below R) s).
  have /sort_sorted_in : {in low_e :: s &, total (@edge_below R)}.
    move=> e1 e2; rewrite !inE =>/orP[/eqP -> |e1in ]/orP[/eqP -> |e2in].
    - apply/orP; left; apply/orP; left; rewrite /point_under_edge.
      by rewrite (eqP (proj1 (pue_formula_two_points _ _)))
              (eqP (proj1 (proj2 (pue_formula_two_points _ _)))) !le_refl.
    - by rewrite alla.
    - by rewrite alla ?orbT.
    - by apply/orP/noc.
  by apply; apply/allP=> x xin /=; apply/orP; right; exact: xin.
have /sub_in1/= trsf : {subset sort (@edge_below R) s <= s}.
  by move=> x; rewrite mainsort.
move/trsf:outs => {}outs.
have [lin hin] : (low_e \in [:: low_e, high_e & s]) /\
   (high_e \in [:: low_e, high_e & s]).
  by split; rewrite !inE eqxx ?orbT.
have slho : {subset (sort (@edge_below _) s) <=
               [:: low_e, high_e & s]}.
  by move=> x; rewrite mainsort => xin; rewrite !inE xin ?orbT.
move=> x xin.
have srt : sorted (@edge_below R) (low_e :: sort (@edge_below R) s).
  case sq : (sort (@edge_below R) s) => [// | a tl].
    rewrite -[sorted _ _]/((low_e <| a) && sorted (@edge_below R) (a :: tl)).
    by rewrite -sq sorted_e andbT alla // -mainsort sq inE eqxx.
have := (opening_cells_aux_right_form _ _ _ _ lin hin lowhigh outs).
move: xin; rewrite /opening_cells.
case: (opening_cells_aux _ _ _ _) => [s1 c1] xin - /(_ s1 c1).
move=> /(_ _ _ _ _ _ _ _ erefl) => it.
by apply: (allP (it _ _ _ _ _ _ _) x xin).
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
have rfc1 : low c1 <| high c1.
  move : op_rf.
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
  by move: op_rf=> /allP /(_ c); rewrite inE eqxx  => /(_ isT).
have underhigh : p <<= (high_c).
  rewrite (_ : high_c = high c); last by rewrite ceq.
  by apply: order_edges_viz_point.
have strictunder : p <<< (low c).
  by move: notcontain; rewrite ceq negb_and /= underhigh orbF negbK.
rewrite /edge_below in rfc1.
move: notcontain; rewrite /contains_point negb_and negbK /==> notcontain.
apply/negP; rewrite negb_and negbK.
by rewrite (strict_under_seq adj_op opvalid op_rf strictunder).
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
cells_bottom_top open_cells ->
inside_box p ->
open_cells_decomposition open_cells p  = (first_cells, contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) -> ~ contains_point p c.
Proof.
move => fc c_c l_c low_f high_f.
rewrite /open_cells_decomposition.
case: open_cells => [ | c q] rfo valo adjo boto inbox_p.
  by move=>[] <- _ <- _ _ c.
move/fix_not_contain; apply => //.
by apply: (bottom_imp_seq_below boto).
Qed.

Lemma decomposition_not_end open_cells e :
forall first_cells contact last_cells low_f high_f,
s_right_form open_cells ->
seq_valid open_cells (point e) ->
adjacent_cells open_cells ->
cells_bottom_top open_cells ->
inside_box (point e) ->
open_cells_decomposition open_cells (point e)  = (first_cells, contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) -> ( ~ event_close_edge (low c) e) /\ ( ~ event_close_edge (high c) e).
Proof.
move=> fc c_c l_c low_f high_f srf svalid adj cbtom inbox_p.
move=> dec_eq c1 c1nfclc.
have := (decomposition_not_contain srf svalid adj cbtom inbox_p dec_eq c1nfclc).
have c1open : c1 \in open_cells.
    rewrite (decomposition_preserve_cells dec_eq).
    move : c1nfclc => /orP [].
      by rewrite mem_cat => -> .
    rewrite !mem_cat => -> .
    by rewrite !orbT.
apply : contrapositive_close_imp_cont.
  apply: (allP srf _ c1open).
by rewrite (seq_valid_low svalid) ?(seq_valid_high svalid) //;
   apply/mapP; exists c1.
Qed.

Lemma lower_edge_new_cells e low_e high_e:
forall new_open_cells,
valid_edge low_e (point e) ->
valid_edge high_e (point e) ->
opening_cells (point e) (outgoing e) low_e high_e = new_open_cells ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
(low (head dummy_cell new_open_cells) == low_e).
Proof.
move=> vle vhe.
rewrite /opening_cells.
case : (sort (@edge_below R) (outgoing e)) => [/= |/= c q] newop.
  by rewrite pvertE // pvertE //= => <- /=.
rewrite pvertE //.
by case: (opening_cells_aux _ _ _ _) => [s1 c1] /= => <- /=.
Qed.

Lemma opening_cells_not_nil out le he p :
  opening_cells p out le he != [::].
Proof.
rewrite /opening_cells; case: (opening_cells_aux _ _ _ _) => [s1 c1].
apply/eqP/rcons_neq0.
Qed.

Lemma higher_edge_new_cells e low_e high_e:
out_left_event e ->
forall new_open_cells,
opening_cells (point e) (outgoing e) low_e high_e =
   new_open_cells ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
(high (last dummy_cell new_open_cells) == high_e).
Proof.
rewrite /opening_cells.
move=> /outleft_event_sort outl + + vle vhe.
have := opening_cells_aux_high_last vle vhe outl.
case : (opening_cells_aux _ _ _ _) => [s1 c1] <- ? <-.
by rewrite last_rcons.
Qed.

Lemma lhc_dec open p fc cc lc le he:
  cells_bottom_top open -> adjacent_cells open ->
  inside_box p ->
  open_cells_decomposition open p =  (fc, cc, lc, le, he) ->
  {lec & { hec & { cc' | 
       open = fc ++ cc ++ lc /\
       low lec = le /\ high hec = he /\ cc = lec :: cc' /\
       hec = last lec cc'}}}.
Proof.
move=> cbtom adj inbox_p oe.
have[/eqP <- [/eqP <- ]] :=
 l_h_c_decomposition oe (exists_cell cbtom adj inbox_p).
rewrite (decomposition_preserve_cells oe).
by case: cc {oe} => [// | lec cc']; exists lec, (last lec cc'), cc'.
Qed.

Lemma l_h_in_open (open : seq cell) p :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
exists lc hc, lc \in open /\ hc \in open /\ low lc =
   snd(fst (open_cells_decomposition open p)) /\
   high hc = snd (open_cells_decomposition open p).
Proof.
move=> cbtom adj inbox_p.
case oe : (open_cells_decomposition open p) => [[[[fc cc] lc] le] he].
move: (lhc_dec cbtom adj inbox_p oe) => [lec [hec [cc' [A [B [C [D E]]]]]]].
exists lec, hec.
split; first by rewrite A D /= !(mem_cat, inE) eqxx !orbT.
split; first by rewrite A D E !(mem_last, mem_cat, inE) !orbT.
split; first by rewrite B.
by rewrite C.
Qed.

Lemma opening_cells_close event low_e high_e future :
valid_edge low_e (point event) ->
valid_edge high_e (point event) ->
out_left_event event ->
end_edge low_e future -> end_edge high_e future ->
close_out_from_event event future ->
close_alive_edges (opening_cells (point event) (outgoing event) low_e high_e)
   future.
Proof.
rewrite /opening_cells.
move=> vle vhe oute A B /close_out_from_event_sort; move: A B.
have : {in sort (@edge_below _) (outgoing event),
          forall g, left_pt g == (point event)}.
  by move=> g; rewrite mem_sort; apply: oute.
move : low_e vle.
elim : (sort (@edge_below R) (outgoing event)) => [| g1 q Ih] /= 
            le vle oute' endl endh.
  move=> _.
  by rewrite pvertE // pvertE //= endl endh.
move => /andP[] endg1 allend.
have oute1 : {in q, forall g, left_pt g == point event}.
  by move=> g gin; apply oute'; rewrite inE gin orbT.
have vg1 : valid_edge g1 (point event).
  by rewrite -(eqP (oute' g1 _)) ?valid_edge_left // inE eqxx.
have:= Ih g1 vg1 oute1 endg1 endh allend.
case : (opening_cells_aux _ _ _ _) => [s1 c1] => {}Ih.
by rewrite pvertE //= endl endg1 Ih.
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
rewrite /= => /andP [] linfh _.
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
have := exists_cell cbtop adjopen insbox => [][]c' cin cont.
have exi : (exists c0 : cell, (c0 \in c :: q) && contains_point p c0).
  exists c'.
  by rewrite cin (contains_point'W cont).
rewrite /open_cells_decomposition => op_f. 
by have := (l_h_above_under_fix exi op_f) => /andP [].
Qed. 

Lemma l_h_above_under_strict open p :
cells_bottom_top open -> adjacent_cells open  ->
inside_box p ->
seq_valid open p ->
s_right_form open ->
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition open p  =
   (first_cells, contact, last_cells, low_f, high_f) ->
  p >>> low_f /\ p <<< high_f.
Proof.
move => cbtom adj inbox_p val rfo  fc cc lc le he oe.
have [lec [hec [cc' [ocd [leq [heq [ccq hecq]]]]]]]:=
      lhc_dec cbtom adj inbox_p oe.
have notc := decomposition_not_contain rfo val adj cbtom inbox_p oe.
move: (inbox_p)=> /andP[] /andP[] pab plt _.
have [pale puhe] := l_h_above_under cbtom adj inbox_p val oe.
split.
  elim/last_ind: {2} (fc)  (erefl fc) => [ fceq | fc' lfc _ fceq].
    by move: cbtom; rewrite ocd fceq ccq -leq => /andP[] /andP[] _ /= /eqP ->.
  have lfco : lfc \in open by rewrite ocd fceq !(mem_cat, mem_rcons, inE) eqxx.
  move: adj; rewrite ocd ccq /= -adjacent_cut; last first.
    by rewrite fceq; case : (fc').
  rewrite fceq /= last_rcons -leq.
  move => /andP[] /andP[] /eqP /[dup] A <- _ _; apply/negP=> abs.
  have := notc lfc; rewrite fceq mem_rcons inE eqxx => /(_ isT).
  rewrite /contains_point abs andbT=> /negP; rewrite negbK => abs' {abs}.
  case/negP: pale.
  move: rfo => /allP /(_ lfc lfco) lbh.
  have [vall valh]:= andP (allP val lfc lfco).
  by rewrite -leq -A (order_edges_strict_viz_point vall valh).
case lceq : lc => [ | hlc lc'].
  move: cbtom; rewrite ocd lceq ccq cats0 -heq=> /andP[]/andP[] _ _.
  by rewrite last_cat /= -hecq => /eqP ->.
have hlco : hlc \in open by rewrite ocd lceq !(mem_cat, inE) eqxx !orbT.
move: adj; rewrite ocd catA lceq -adjacent_cut; last by rewrite ccq; case: (fc).
move=> /andP[] /andP[] + _ _; rewrite ccq last_cat /= -hecq heq.
move => /eqP /[dup] A ->.
rewrite -(negbK (_ <<< _)); apply/negP=> abs.
have := notc hlc; rewrite lceq inE eqxx orbT => /(_ isT).
rewrite /contains_point abs /=; apply => {abs}.
move: rfo => /allP /(_ hlc hlco) => lbh.
have [vall valh]:= andP (allP val hlc hlco).
by rewrite (order_edges_viz_point vall valh) // -A.
Qed.

Lemma higher_lower_equality e open :
out_left_event e ->
forall first_cells contact_cells last_cells low_e high_e,
open_cells_decomposition open (point e) =
(first_cells, contact_cells, last_cells, low_e, high_e) ->
forall new_cells,
(opening_cells (point e) (outgoing e) low_e high_e) =
  new_cells ->
(exists2 c : cell, c \in open & contains_point' (point e) c) ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
low (head dummy_cell contact_cells) = low (head dummy_cell new_cells) /\
high (last dummy_cell contact_cells) = high (last dummy_cell new_cells) /\ contact_cells != nil.
Proof.
move => outleft fc c_c lc lowe highe op_c_d new_cells op_new exi lowv highv.
have := (lower_edge_new_cells lowv highv op_new lowv highv) => /eqP low_new.
have := (higher_edge_new_cells outleft op_new lowv highv) => /eqP high_new.
have := (l_h_c_decomposition op_c_d  exi).
move => [] /eqP l_old [] /eqP h_old c_nnil.
by rewrite low_new high_new l_old h_old .
Qed.

Lemma opening_valid e low_e high_e:
out_left_event e ->
valid_edge low_e (point e) ->
valid_edge high_e (point e) ->
seq_valid (opening_cells (point e) (outgoing e) low_e high_e) (point e).
Proof.
move=> + + vhe.
rewrite /opening_cells.
move/outleft_event_sort.
move : low_e.
elim : (sort (@edge_below R) (outgoing e)) => [/= | c q IH] low_e outl vle.
  rewrite /=.
  by rewrite pvertE // pvertE //= vle vhe.
rewrite /=.
rewrite pvertE //.
have vc : valid_edge c (point e).
  by rewrite -(eqP (outl c _)) ?valid_edge_left // inE eqxx.
have outl1 : forall g, g \in q -> left_pt g == point e.
  by move=> g gin; rewrite outl // inE gin orbT.
have := IH c outl1 vc.
case: (opening_cells_aux _ _ _ _) => [s1 c1] {} Ih /=.
by rewrite vle vc Ih.
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
rewrite /opening_cells.
have dec_not_end :=
  decomposition_not_end srf val_op_e adjop cbtop insboxe op_dec.
have open_eq := decomposition_preserve_cells op_dec.
have := (l_h_valid cbtop adjop  insboxe val_op_e op_dec) => [][] lowv highv.
rewrite open_eq in val_op_e.
have exi := exists_cell cbtop adjop insboxe.
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top open_eq => /andP [] /andP [] _ /eqP openbottom /eqP opentop.
have := (open_not_nil (sort (@edge_below R) (outgoing e)) lowv highv).
case op_new : (opening_cells_aux (point e) _ low_e high_e)
   => [//=| cnew q'' /=] _.
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
rewrite /opening_cells op_new in close_new.
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
{in future_events, forall e', lexePt p (point e')} ->
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
rewrite /opening_cells => -[] open2eq _.
rewrite -open2eq in close_all.
rewrite -open2eq{open2eq}.
have dec_not_end :=
   decomposition_not_end srf val_op_e adjop cbtop insboxe op_dec.
have open_eq := decomposition_preserve_cells op_dec.

have := (l_h_valid cbtop adjop  insboxe val_op_e op_dec) => [][] lowv highv.
rewrite open_eq in val_op_e.
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top open_eq => /andP [] /andP [] _ /eqP openbottom /eqP opentop.
have := (open_not_nil (sort (@edge_below R) (outgoing e)) lowv highv).
case op_new : (opening_cells_aux (point e) _ low_e high_e)
   => [//= | cnew q'' /=] _.
have := higher_lower_equality outlefte op_dec op_new exi lowv highv .
rewrite /= => [][] low_eq [] high_eq ccnnil.

case : cc op_dec open_eq val_op_e openbottom opentop low_eq high_eq ccnnil lhc => [//|c q  /=] op_dec open_eq val_op_e openbottom opentop low_eq high_eq ccnnil lhc.
have := opening_valid outlefte lowv highv; rewrite /opening_cells.
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
  opening_cells_aux p s le he = new -> 
  adjacent_cells new /\ (new != nil -> low (head dummy_cell new) = le).
Proof.
elim: s le new => [ | g s Ih] le new /=; set vip := vertical_intersection_point.
  case vip1 : (vip R p le) => [p1 | ]; last by move=> <-.
  case vip2 : (vip R p he) => [p2 | ]; last by move=> <-.
  by case: ifP => _ <- //=.
case: (vip R p le) => [p1 | ]; last by move=> <-.
by case: ifP => testres <- //=;
  (split; last by [];
  move: (Ih g _ erefl) => []; case: (opening_cells_aux _ _ _ _) => //=;
  move=> a l -> ->; rewrite // eqxx).
Qed.

Lemma adjacent_opening' p s le he:
  adjacent_cells (opening_cells_aux p s le he).
Proof.
case: s => [| g s ] /=; set vip := vertical_intersection_point.
  case vip1 : (vip R p le) => [p1 | ]; last by [].
  by case vip2 : (vip R p he) => [p2 | ].
case: (vip R p le) => [p1 | ]; last by [].
rewrite /=.
move: (@adjacent_opening_aux' p s g he _ erefl).
case: (opening_cells_aux _ _ _ _) => //=.
by move=> a l [] -> ->; rewrite // eqxx.
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
rewrite /opening_cells.
move => [] <- _ adjopen.
have exi := (exists_cell cbtop adjopen insbox ).
have openeq := decomposition_preserve_cells op_c_d.
have := (l_h_valid cbtop adjopen  insbox validopen op_c_d).
move => [] lowv highv.
have := (open_not_nil (sort (@edge_below R) (outgoing e)) lowv highv).
case op_new : (opening_cells_aux (point e) _ low_e high_e)
  => [//= | q l ] qlnnil.
have := higher_lower_equality outleft op_c_d op_new exi lowv highv => [][] l_eq [] h_eq c_nnil.
have adjnew : adjacent_cells (q :: l).
  by rewrite -op_new; apply:adjacent_opening'.
rewrite openeq in adjopen.
apply : (replacing_seq_adjacent c_nnil qlnnil l_eq h_eq adjopen adjnew).
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
rewrite /opening_cells.
move => [] <- _.
have := (l_h_valid cbtop adjopen insbox openvalid op_c_d).
move => [] lowv highv.
have exi := (exists_cell cbtop adjopen insbox ).
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top => /andP [] /andP [] opnnil /eqP openbottom /eqP _.
have newnnil := open_not_nil (sort (@edge_below R) (outgoing e)) lowv highv.
have newopnnil := (middle_seq_not_nil first_cells last_cells newnnil).
rewrite newopnnil /=.
case op_new : (opening_cells_aux (point e) _ low_e high_e) => [// | c q].
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
rewrite /opening_cells.
have op_dec := (decomposition_preserve_cells op_c_d).
move => [] <- _.
have := (l_h_valid cbtop adjopen insbox openvalid op_c_d).
move => [] lowv highv.
have exi := (exists_cell cbtop adjopen insbox ).
move : cbtop.
rewrite /cells_bottom_top /cells_low_e_top => /andP [] /andP [] opnnil /eqP _ /eqP opentop.
have newnnil := open_not_nil (sort (@edge_below R) (outgoing e)) lowv highv.
have newopnnil := (middle_seq_not_nil first_cells last_cells newnnil).
case op_new : (opening_cells_aux (point e) _ low_e high_e) => [// | c q].
  by rewrite op_new in newnnil.
have := higher_lower_equality outleft op_c_d op_new exi lowv highv => [][] _ [] /= h_eq c_nnil.
case : last_cells op_c_d op_dec newopnnil => [/= op_c_d |c1 q1 _ op_dec /=]  .
  rewrite !cats0 -opentop last_cat  => -> newn_nil /=.
  rewrite last_cat -h_eq.
  by case  : contact_cells c_nnil h_eq op_c_d.
by rewrite -opentop op_dec !last_cat /= last_cat.
Qed.

Lemma opening_cells_last_lexePt e low_e high_e c :
out_left_event e ->
~~(point e <<< low_e) -> point e <<< high_e ->
valid_edge low_e (point e)-> valid_edge high_e (point e) ->
{in  (rcons (low_e::(sort (@edge_below R) (outgoing e))) high_e) &, no_crossing R} ->
low_e <| high_e ->
 c \in (opening_cells (point e) (outgoing e) low_e high_e) ->
 lexePt (last dummy_pt (left_pts c)) (point e).
Proof.
rewrite /opening_cells.
move => /outleft_event_sort outlefte eabl eunh lowv highv .

elim : (sort (@edge_below R) (outgoing e)) low_e eabl lowv outlefte => [/= | c' q IH] low_e eabl lowv outlefte nc linfh.
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
have outq: (forall e0 : edge_eqType R, e0 \in q -> left_pt e0 == point e).
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
have nc' : {in  (rcons (c'::q) high_e) &, no_crossing R}.
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
  {in [seq low c | c <- open] ++ [seq high c | c <- open] &, no_crossing R} ->
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
have [e1 e2]:= l_h_above_under_strict cbtom adj insp valp r_f op_c_d_eq.
case/negP: e1.
have [vl vh]  : valid_edge le p /\ valid_edge he p.
  by split; move: valp =>/[dup]/allP/(_ _ lcin)/andP[] + +
             /allP/(_ _ hcin)/andP[]; rewrite le_eq he_eq.
by have /underW := (order_edges_strict_viz_point' vh vl abs_he_under_le e2).
Qed.

Lemma step_keeps_left_pts_inf' e (future_events : seq event) old_open : 
inside_box (point e) -> out_left_event e ->
s_right_form old_open -> seq_valid old_open (point e) ->
adjacent_cells old_open -> cells_bottom_top old_open ->
close_alive_edges old_open (e :: future_events) ->
close_edges_from_events (e :: future_events) ->
{in  all_edges old_open (e :: future_events) &, no_crossing R} ->
bottom_left_cells_lex old_open (point e) ->
forall new_open new_closed closed,
step e old_open closed  = (new_open, new_closed) ->
forall c, c \in new_open -> lexePt (bottom_left_corner c) (point e).
Proof.
move => insboxe outlefte srf openval adjopen cbtom close_ed close_ev  n_c old_keep_left new_open new_closed closed step.
move => c cin.
have cbtop_new := step_keeps_bottom_top insboxe openval adjopen cbtom outlefte step.
have adj_new := step_keeps_adjacent insboxe outlefte openval cbtom step adjopen.
move : step.
rewrite /step.
case op_c_d : (open_cells_decomposition old_open (point e)) =>  [[[[first_cells contact_cells] last_cells ]low_e] high_e].
have ocd := (decomposition_preserve_cells op_c_d).
move => [] new_eq _.
move : cin.
rewrite ocd in old_keep_left.
rewrite -new_eq !mem_cat orbCA => /orP [| /orP [cin | cin]]; first last.
    by apply/lexPtW/old_keep_left; rewrite !mem_cat cin !orbT.
  by apply/lexPtW/old_keep_left; rewrite !mem_cat cin.
move => cin. 
have [lowinfe einfhigh] :=
   l_h_above_under_strict cbtom adjopen insboxe openval srf op_c_d.
have [vallow valhigh]:= l_h_valid cbtom adjopen insboxe openval op_c_d.
have linfh : low_e <| high_e.
  have n_c' : {in [seq low i | i <- old_open] ++ [seq high i | i <- old_open] &,
                 no_crossing R}.
    have sub_cat (s1 s2 : seq edge): forall x, x \in s1 -> x \in s1 ++ s2.
      by move=> x; rewrite mem_cat => ->.
    by move: n_c; rewrite /all_edges /cell_edges=> /(sub_in2 (sub_cat _ _)).
  by apply: open_cells_decomposition_low_under_high _ _ _ _ _ op_c_d.
have n_c' : {in rcons (low_e :: sort (@edge_below R) (outgoing e)) high_e &, no_crossing R}.
  have [lc1 [lc2 [lc1in [lc2in]]]] := l_h_in_open cbtom adjopen insboxe.
    rewrite op_c_d /= => [][lowlc1 highlc2].
  have subseq:
    forall x, x \in rcons (low_e :: sort (@edge_below R) (outgoing e)) high_e ->
          x \in all_edges old_open (e :: future_events).
    move=> x; rewrite -cats1 mem_cat 2!inE 2!mem_cat orbAC=> /orP[].
      by move=>/orP[]/eqP ->; rewrite -?lowlc1 -?highlc2 map_f ?orbT.
    rewrite mem_sort=> xin; apply/orP; right.
    by apply/flattenP; exists (outgoing e); rewrite // inE eqxx.
  by apply: (sub_in2 subseq).
have lowinfe' : ~~ (point e <<< low_e).
  move : lowinfe => lowinfe.
  apply (underWC lowinfe).
exact: (opening_cells_last_lexePt outlefte lowinfe' _ _ _ n_c' linfh cin).
Qed.

Lemma step_keeps_left_pts_inf e (future_events : seq event) p old_open : 
inside_box (point e) -> out_left_event e ->
s_right_form old_open -> seq_valid old_open (point e) ->
adjacent_cells old_open -> cells_bottom_top old_open ->
close_alive_edges old_open (e :: future_events) ->
close_edges_from_events (e :: future_events) ->
{in  all_edges old_open (e :: future_events) &, no_crossing R} ->
bottom_left_cells_lex old_open (point e) ->
forall new_open new_closed closed,
step e old_open closed  = (new_open, new_closed) ->
(lexPt (point e) p) ->
bottom_left_cells_lex new_open p.
Proof.
move=> inbox_e out_e rfo sval adj cbtom clae clee noc old_keep_left.
move=> new_open new_closed closed stepeq einfp c cin.
apply: (lexePt_lexPt_trans _ einfp).
by apply: (step_keeps_left_pts_inf' _ _ _ _ _ _ clae _ _ _ stepeq).
Qed.

Lemma step_keeps_right_form e open closed op2 cl2 :
  cells_bottom_top open -> adjacent_cells open -> 
  inside_box (point e) -> seq_valid open (point e) ->
  {in ([seq low c | c <- open] ++ [seq high c | c <- open]) ++
      outgoing e &, no_crossing R} ->
  out_left_event e ->
  s_right_form open ->
  step e open closed = (op2, cl2) ->
  s_right_form op2.
Proof.
move=> cbtom adj inbox_e sval noc oute rfo; rewrite /step /=.
case oe : (open_cells_decomposition open (point e)) => [[[[fc cc] lc] le] he].
move=> [] <- _.
have [c1 [c2 [cc' [ocd [le_eq [he_eq [cceq lceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
have c1in : c1 \in open by rewrite ocd cceq !(mem_cat, inE, eqxx, orbT).
have c2in : c2 \in open.
  by rewrite ocd cceq !mem_cat lceq mem_last !orbT.
have [lP hP] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
set bigs := cell_edges open ++ outgoing e.
have lein : le \in bigs by rewrite -le_eq !mem_cat map_f.
have hein : he \in bigs by rewrite -he_eq !mem_cat map_f ?orbT.
have obig : {subset outgoing e <= bigs}.
  by move=> g gin; rewrite !mem_cat gin orbT.
have lev : valid_edge le (point e) by have [] := l_h_valid _ _ _ _ oe.
have hev : valid_edge he (point e) by have [] := l_h_valid _ _ _ _ oe.
have [edgesabove edgesbelow nocout] :=
   outgoing_conditions lP hP lein hein lev hev obig noc oute.
have /allP rfn : s_right_form 
    (opening_cells (point e) (outgoing e) le he).
  apply: (opening_cells_right_form hev (underWC lP) hP _ oute) => //.
  apply: (edge_below_from_point_under _ _ _ (underW hP) lP) => //.
  by apply: noc; rewrite -?le_eq -?he_eq !mem_cat map_f ?orbT.
apply/allP=> x; rewrite !mem_cat orbCA=> /orP[/rfn// | ].
by move=> xin; apply: (allP rfo); rewrite ocd !mem_cat orbCA xin orbT.
Qed.

Lemma size_open_ok (p : pt) (out : seq edge) (low_e : edge) (high_e : edge) :
valid_edge low_e p ->
valid_edge high_e p ->
(forall e, e \in out -> left_pt e == p) ->
let open :=  opening_cells_aux p out low_e high_e in
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

Lemma cell_edges_opening_cells p s le he :
  {subset cell_edges (opening_cells p s le he) <= s ++ [:: le; he]}.
Proof.
by move=> g; rewrite mem_cat=>/orP[] /mapP[c cin ->];
  have := opening_cells_subset cin => /andP[]; rewrite !(mem_cat, inE) =>
    /orP[A | B] /orP[C | D]; rewrite ?A ?B ?C ?D ?orbT.
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
   (opening_cells (point e) (outgoing e) le he) <=
      cell_edges open ++ outgoing e}.
  move=> g /cell_edges_opening_cells; rewrite !mem_cat=>/orP[-> | loh].
    by rewrite orbT.
  have [cle [che [clein [chein]]]] := l_h_in_open cbtom adj inbox_e.
  move: loh => /[swap]; rewrite oe /= !inE => -[<- <-] /orP[]/eqP ->.
    by apply/orP; left; apply/orP; left; apply/mapP; exists cle.
  by apply/orP; left; apply/orP; right; apply/mapP; exists che.
move=> <- _ x.
rewrite !cell_edges_cat mem_cat !cell_edges_cat [X in _ || X]mem_cat.
rewrite orbCA=> /orP[ | fclc ]; first by apply: new.
rewrite dcp mem_cat cell_edges_catCA. 
by rewrite cell_edges_cat mem_cat cell_edges_cat [X in _ || X || _]mem_cat fclc orbT.
Qed.

Lemma no_dup_seq_x3 e2 a b c:
  vertical_intersection_point a e2 = Some c ->
  p_x (last dummy_pt (no_dup_seq [:: b; a; c])) = p_x a.
Proof.
move => /intersection_on_edge [_ cq]; rewrite /=.
by repeat (case: ifP=> _ /=).
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

Lemma closing_cells_single_map p cc :
  closing_cells p cc = map (close_cell p) cc.
Proof. by []. Qed.

Lemma leftmost_points_max :
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  left_limit (start_open_cell bottom top) =
  max (p_x (left_pt bottom)) (p_x (left_pt top)).
Proof.
rewrite /start_open_cell /leftmost_points => /andP[] /=.
case: ltrP => cmpl.
  case peq: (vertical_intersection_point (left_pt top) bottom) => [p' | //].
  move=> _ /andP[] samex _ /=.
  move: peq; rewrite /vertical_intersection_point.
  by case: ifP=> // ve [] <-.
case peq: (vertical_intersection_point (left_pt bottom) top)=> [p' | //].
by move=> _ /andP[].
Qed.

Lemma opening_cells_aux_side_limit e s le he :
  valid_edge le e -> valid_edge he e -> le <| he ->
  e >>= le -> e <<< he ->
  {in [:: le, he & s] &, no_crossing R} ->
  {in s, forall g, left_pt g == e} ->
  all open_cell_side_limit_ok (opening_cells_aux e s le he).
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
suff/allP/(_ c cintl) :
   all open_cell_side_limit_ok (opening_cells_aux e s g he).
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

Lemma opening_cells_side_limit e s le he :
  valid_edge le e -> valid_edge he e -> le <| he ->
  e >>= le -> e <<< he ->
  {in [:: le, he & s] &, no_crossing R} ->
  {in s, forall g, left_pt g == e} ->
  all open_cell_side_limit_ok (opening_cells e s le he).
Proof.
move=> vle vhe bel ea eu noc lefts.
apply: opening_cells_aux_side_limit => //; last first.
  move=> g; rewrite (perm_mem (permEl (perm_sort _ _))); apply: lefts.
move=> g1 g2; rewrite !inE !(perm_mem (permEl (perm_sort _ _)))=> g1in g2in.
by apply: noc.
Qed.

Lemma opening_cells_below_high p e c s le he:
  le <| he ->
  (e >>> le) && (e <<< he) ->
  valid_edge le e ->
  valid_edge he e ->
  valid_edge he p -> (forall g, g \in s -> left_pt g == e) ->
  {in le::he::s &, no_crossing R} ->
  c \in opening_cells e s le he -> strict_inside_open p c -> p <<< he.
Proof.
move=> lowhigh ebounds vle vhe vp gleft noc oc /andP[]/andP[] plhc _ lims.
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
by apply: (valid_high_limits cok); move: lims=> /andP[] -> /ltW ->.
Qed.

Lemma opening_cells_above_low p e c s le he:
  le <| he ->
  (e >>> le) && (e <<< he) ->
  valid_edge le e ->
  valid_edge he e ->
  valid_edge le p -> (forall g, g \in s -> left_pt g == e) ->
  {in le:: he :: s &, no_crossing R} ->
  c \in opening_cells e s le he -> strict_inside_open p c -> p >>> le.
Proof.
move=> lowhigh ebounds vle vhe vp gleft noc oc /andP[]/andP[] _ palc lims.
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
by apply: (valid_low_limits cok); move: lims=> /andP[] -> /ltW ->.
Qed.

Lemma opening_cells_aux_disjoint (s oe : seq edge) p le he :
    p >>> le -> p <<< he -> le \in s -> he \in s -> le <| he ->
    valid_edge le p -> valid_edge he p -> {subset oe <= s} ->
    {in s &, no_crossing R} -> {in oe, forall g : edge, left_pt g == p} ->
    path (@edge_below R) le oe ->
    {in opening_cells_aux p oe le he &, disjoint_open_cells R}.
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
suff main : forall c, c \in opening_cells_aux p oe og he -> o_disjoint_e W c.
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
have oc0q : opening_cells_aux p (og :: oe) le he =
   W :: opening_cells_aux p oe og he.
  by rewrite /= vip.
have noc' : {in [:: le, he , og & oe] &, no_crossing R}.
  move: noc; apply: sub_in2 => g; rewrite 2!inE.
  by move=> /orP[/eqP ->| /orP[/eqP -> | ginoe]] //; apply: oesub.
have/allP cok := opening_cells_aux_side_limit vl vh lowhigh pl ph noc' leftg.
have [ | qnW//] :=  boolP(inside_open' q W).
  move=> /andP[]/andP[] /andP[] _ Main2 /andP[] _ w2 /andP[] Main1 w1/=.
have vhwq : valid_edge (high W) q.
  apply: valid_high_limits; last by rewrite w1 w2.
  by apply: cok; rewrite oc0q inE eqxx.
have adj0 := adjacent_opening' p (og :: oe) le he.
have rf0 := opening_cells_aux_right_form pl ph vh lein hein lowhigh leftg noc
         oesub soe.
have := seq_edge_below' adj0 rf0; rewrite oc0q [head _ _]/= => srt.
have vog : valid_edge og q by move: vhwq; rewrite [high W]/=.
case ocq : (opening_cells_aux p oe og he) => [| c0 q0].
  by move: cin; rewrite ocq.
move: adj0; rewrite /= ocq vip /= => /andP[/eqP ogl adj'].
move: vog; rewrite ogl=> vog.
move: (cin) => /(nthP W) [rank rltsize /esym ceq].
have {}ceq : c = nth W (c0 :: q0) rank by move: ceq; rewrite ocq.
case rankeq: rank => [ | rank'].
  have cc0 : c = c0 by rewrite ceq rankeq.
  rewrite cc0 /inside_open'/inside_open_cell/contains_point -ogl.
  by move: Main2; rewrite /= => ->; rewrite ?andbF.
have cq0 : c \in q0.
  have/(mem_nth W) : (rank' < size q0)%N.
    by rewrite -ltnS -[(size _).+1]/(size (c0 :: q0)) -ocq -rankeq.
  by rewrite -[nth _ _ _]/(nth W (c0::q0) rank'.+1) -rankeq -ceq.
apply/negP; rewrite /inside_open'/inside_open_cell => inc.
have valq : valid_edge (low c) q.
  apply: valid_low_limits.
    by apply: cok; rewrite oc0q ocq !inE cq0 ?orbT.
  by move: inc=> /andP[] /andP[] _ /andP[] _ -> /andP[] _ ->.
have tr : {in (og :: oe) & & , transitive (@edge_below R)}.
  apply: (@edge_below_trans R p); last by move: noc; apply: sub_in2.
    by left; move=> g gin; rewrite -(eqP (leftg g gin)) edge_cond.
  by move=> g gin; apply: valid_edge_extremities; rewrite leftg ?eqxx.
have  : all (mem (og :: oe)) [seq low i | i <- opening_cells_aux p oe og he].
  apply/allP=> g /mapP [c2 c2p1 ->].
  by have := opening_cells_aux_subset c2p1=> /andP[].
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
have qu:= order_edges_viz_point' vhwq valq (pathconcl lowcin) Main2.
by move: inc; rewrite qu !andbF.
Qed.

Lemma close_cell_ok e c :
  contains_point e c ->
  valid_edge (low c) e -> valid_edge (high c) e ->
  open_cell_side_limit_ok c ->
  closed_cell_side_limit_ok (close_cell e c).
Proof.
move=> ctp vl vh.
rewrite /open_cell_side_limit_ok/closed_cell_side_limit_ok.
rewrite /close_cell /=; have /exists_point_valid [p1 /[dup] vip1 ->] := vl.
have /exists_point_valid [p2 /[dup] vip2 -> /=] := vh.
move=> /andP[] -> /andP[]-> /andP[]-> /andP[] -> -> /=.
have [o1 x1]:=intersection_on_edge vip1; have [o2 x2]:=intersection_on_edge vip2.
rewrite -?(eq_sym e).
case:ifP=>[/eqP q1 | enp1];case:ifP=>[/eqP q2 | enp2]; move: (o1) (o2);
 rewrite /=  -?q1 -?q2 -?x1 -?x2 ?eqxx/= => -> ->; rewrite ?andbT //=.
- move: ctp=> /andP[] _ eh.
  by apply: (under_edge_strict_lower_y x2 (negbT enp2) eh).
- move: ctp=> /andP[] el _.
  by apply: (above_edge_strict_higher_y x1 (negbT enp1) el).
move: ctp=> /andP[] el eh.
by rewrite (above_edge_strict_higher_y x1 (negbT enp1) el) //
      (under_edge_strict_lower_y x2 (negbT enp2) eh).
Qed.

Lemma closing_cells_side_limit' e cc :
  s_right_form cc ->
  seq_valid cc e ->
  adjacent_cells cc ->
  all open_cell_side_limit_ok cc ->
  all (contains_point e) cc ->
  e >>> low (head dummy_cell cc) ->
  e <<< high (last dummy_cell cc) ->
  all (@closed_cell_side_limit_ok _) (closing_cells e cc).
Proof.
move=> rf val adj oks ctps abovelow belowhigh.
rewrite /closing_cells.
rewrite all_map.
apply/allP=> //= c cin.
have vlc : valid_edge (low c) e by have := (allP val c cin) => /andP[].
have vhc : valid_edge (high c) e by have := (allP val c cin) => /andP[].
apply: close_cell_ok=> //.
  by apply: (allP ctps).
by apply: (allP oks).
Qed.

Lemma open_limit_close_cell p c :
  open_limit (close_cell p c) = open_limit c.
Proof.
rewrite /close_cell.
case : (vertical_intersection_point p (low c)) => [p1 | ]//.
by case : (vertical_intersection_point p (high c)) => [p2 | ].
Qed.

Lemma close'_subset_contact p q c :
  valid_cell c p ->
  closed_cell_side_limit_ok (close_cell p c) ->
  inside_closed' q (close_cell p c) -> inside_open' q c.
Proof.
move=>[] vl vh.
move=>/closed_right_imp_open.
rewrite inside_open'E // inside_closed'E /close_cell.
have [p1 vip1] := exists_point_valid vl.
have [p2 vip2] := exists_point_valid vh.
rewrite vip1 vip2 /= => cok /andP[] -> /andP[] -> /andP[] -> rlim /=.
by apply: (le_trans rlim cok).
Qed.

Lemma close_cell_right_limit p c :
  valid_cell c p ->
  right_limit (close_cell p c) = p_x p.
Proof.
move=> [vl vh].
rewrite /close_cell; rewrite !pvertE // /right_limit /=.
by case: ifP=> cnd1 //; case: ifP=> cnd2.
Qed.

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
move: adje; rewrite /= -[bottom]/(high extra_bot) ocd.
rewrite ccdec -catA cat_path /= => /andP[] _.
by rewrite loc -[bottom]/(high extra_bot) last_map=> /andP[] /eqP.
Qed.

Lemma head_last_cells_low open p fc cc lc le he :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  open_cells_decomposition open p = (fc, cc, lc, le, he) ->
  head top [seq low i | i <- lc] = he.
Proof.
move=> cbtom adj inbox_p oe.
have ctn := exists_cell cbtom adj inbox_p.
have ocd := decomposition_preserve_cells oe.
have [loc [/eqP hic ccn0]] := l_h_c_decomposition oe ctn.
have [cc'  ccdec] : exists cc', cc = rcons cc' (last dummy_cell cc).
  by elim/last_ind: (cc) ccn0 => [// | v *]; rewrite last_rcons; exists v.
have adje : adjacent_cells (extra_bot :: open).
  move: cbtom=> /andP[] /andP[] + + _.
  by move: adj; case: (open) => [ | c s]//= -> _ /eqP ->; rewrite eqxx.
move: adje; rewrite  ocd.
move: cbtom=>/andP[] /andP[] _ _.
rewrite ocd ccdec; case: (lc) => [ | flc lc' _].
  by rewrite cats0 last_cat last_rcons /= hic eq_sym => /eqP.
rewrite /= 2!cat_path last_rcons /= eq_sym => /andP[] _ /andP[] _ /andP[] + _.
by rewrite hic=> /eqP.
Qed.

Lemma high_in_first_cells_below open p first_cells cc last_cells le he :
  open_cells_decomposition open p =
  (first_cells, cc, last_cells, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  seq_valid open p ->
  s_right_form open ->
  {in cell_edges open &, no_crossing R} ->
  {in [seq high i | i <- first_cells], forall g, p_x p < p_x (right_pt g)} ->
  {in [seq high c | c <- first_cells], forall g, g <| le}.
Proof.
move=> oe cbtom adj inbox_e sval rfo noc side_cond.
have ocd := decomposition_preserve_cells oe.
have vfc : {in [seq high i | i <- first_cells], forall g, valid_edge g p}.
  move=> g /mapP[c cin geq]; apply: (seq_valid_high sval).
  by apply/mapP; exists c=> //; rewrite ocd !mem_cat cin.
move=> g /mapP[c cin geq].
have [fc1 [fc2 fceq]] := mem_seq_split cin.
have cin' : c \in open by rewrite ocd !(mem_cat, inE) cin.
have := seq_edge_below' adj rfo; rewrite ocd fceq -[c :: _]/([:: c] ++ _).
set w := head _ _; rewrite -!catA (catA fc1) map_cat cat_path=> /andP[] _.
have tr : {in [seq high i | i <- first_cells] & &, transitive (@edge_below R)}.
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

Lemma all_edges_opening_cells_above_first e open fc cc lc le he outg:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  s_right_form open ->
  seq_valid open (point e) ->
  inside_box (point e) ->
  {in cell_edges open ++ outg, forall g, inside_box (left_pt g)} ->
  {in cell_edges fc, forall g, p_x (point e) < p_x (right_pt g)} ->
  {in cell_edges open ++ outg &, no_crossing R} ->
  {in outg, forall g, left_pt g == (point e)} ->
  {in cell_edges fc &
      [seq high i | i <- (opening_cells_aux (point e) outg le he)],
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
have noc' : {in cell_edges open &, no_crossing R}.
  by move: noc; apply: sub_in2=> g gin; rewrite mem_cat gin.
rewrite (cell_edges_high fcn0 adjf) inE => /orP[/eqP -> | ].
  rewrite hdfc=> gin0.
  have gin : g2 \in outg ++ [:: he].
      move: gin0=>/mapP[c /opening_cells_aux_subset /andP[] _ hiin geq].
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
  by apply: (seq_valid_high sval); apply/mapP; exists c1.
have [vle vhe] : valid_edge le (point e) /\ valid_edge he (point e).
  by have [] := l_h_valid cbtom adj inbox_e sval oe.
have v2' : {in outg, forall g, valid_edge g (point e)}.
  move=> g gin; have /eqP <- : left_pt g == point e by apply: outs.
  by move: (@valid_edge_extremities R g (left_pt g)); rewrite eqxx; apply.
move=> /mapP[c2 /opening_cells_aux_subset /andP[] _ g2in g2eq ].
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
have [egtle elthe]:= l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have lelte: pvert_y (point e) le < p_y (point e).
  by move: egtle; rewrite (under_pvert_y vle) // -ltNge.
have eleg2 : p_y (point e) <= pvert_y (point e) g2.
  rewrite -(under_pvert_y v2).
  move: g2in; rewrite g2eq inE => /orP[ /eqP -> | /outs /eqP <-].
    by rewrite (under_onVstrict vhe) elthe orbT.
  by rewrite left_pt_below.
by apply: lt_le_trans eleg2.
Qed.

(* Temporary trial, but this lemma might be better placed in
  points_and_edges. *)
Lemma decomposition_above_high_fc p open fc cc lc le he c1:
  open_cells_decomposition open p = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  s_right_form open ->
  seq_valid open p ->
  c1 \in fc -> p >>> high c1.
Proof.
move=> oe cbtom adj  inbox_e rfo sval c1in.
have ocd := decomposition_preserve_cells oe.
rewrite under_pvert_y; last first.
    apply: (seq_valid_high sval).
    by apply/mapP; exists c1; rewrite // ocd !mem_cat c1in.
rewrite -ltNge.
have pale : pvert_y p le < p_y p.
  have [+ _] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  rewrite under_pvert_y; last first.
    by have [] := l_h_valid cbtom adj inbox_e sval oe.
  by rewrite -ltNge.
apply: le_lt_trans pale.
move: c1in.
have [fceq | [fc' [lfc fceq]]] : fc = nil \/ exists fc' lfc, fc = rcons fc' lfc.
    by elim/last_ind : (fc) => [ | fc' lfc _];[left | right; exists fc', lfc].
  by rewrite fceq.
have := last_first_cells_high cbtom adj inbox_e oe.
rewrite fceq map_rcons last_rcons => <-.
rewrite mem_rcons inE => /orP[/eqP c1lfc | c1o]; first  by rewrite c1lfc.
have [a [b pab]] := mem_seq_split c1o.
move: fceq; rewrite pab -cats1 -catA /= => fceq.
(* requirement for path_edge_below_pvert_y *)
have req1 : all (valid_edge (R := _) ^~ p)
    [seq high i | i <- c1 :: b ++ [:: lfc]].
  apply/allP; apply: (sub_in1 _ (seq_valid_high sval)); apply: sub_map.
  by rewrite ocd fceq=> x; rewrite 2!mem_cat=> ->; rewrite orbT.
have req2 : path (@edge_below R) (high c1) [seq high i | i <- b ++ [:: lfc]].
  have := seq_edge_below' adj rfo.
  rewrite ocd (_ : fc = rcons a c1 ++ rcons b lfc); last first.
     by move: fceq; rewrite -!cats1 !catA /= -!catA /=.
  rewrite -!catA [X in path _ _ X]map_cat cat_path=> /andP[] _.
  rewrite !map_rcons last_rcons map_cat cat_path => /andP[] + _.
  by rewrite -cats1.
have : path (<=%R) (pvert_y p (high c1))
  [seq pvert_y p (high i) | i <- b ++ [:: lfc]].
  by have := path_edge_below_pvert_y req1 req2; rewrite -map_comp.
rewrite le_path_sortedE => /andP[] /allP + _.
move=> /(_ (pvert_y p (high lfc))); apply.
by apply/mapP; exists lfc => //=; rewrite mem_cat inE eqxx orbT.
Qed.

Lemma decomposition_under_low_lc p open fc cc lc le he c1:
  open_cells_decomposition open p = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  s_right_form open ->
  seq_valid open p ->
  c1 \in lc -> p <<< low c1.
Proof.
move=> oe cbtom adj  inbox_e rfo sval c1in.
have ocd := decomposition_preserve_cells oe.
rewrite strict_under_pvert_y; last first.
    by apply/(seq_valid_low sval)/map_f; rewrite ocd !mem_cat c1in ?orbT.
have puhe : p_y p < pvert_y p he.
  have [ _ ] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  rewrite strict_under_pvert_y //.
 by have [] := l_h_valid cbtom adj inbox_e sval oe.
apply: (lt_le_trans puhe).
move: c1in; case lceq : lc => [ // | flc lc'] c1in.
have := head_last_cells_low cbtom adj inbox_e oe.
rewrite lceq /= => <-.
move: c1in; rewrite inE => /orP[/eqP c1flc | c1o]; first by rewrite c1flc.
have [a [b Pab]] := mem_seq_split c1o.
(* requirement for path_edge_below_pvert_y *)
have req1 : all (@valid_edge R ^~ p)
  [seq low i | i <- flc :: a ++ c1 :: b].
  apply/allP; apply: (sub_in1 _ (seq_valid_low sval)); apply: sub_map.
  rewrite ocd lceq Pab=> x; rewrite 2!mem_cat => ->.
  by rewrite !orbT.
have req2 : path (@edge_below R) (low flc) [seq low i | i <- a ++ c1 :: b].
  have := seq_edge_below' adj rfo.
  have [on0 headq] : open != [::] /\ low (head dummy_cell open) = bottom.
    by move: cbtom=> /andP[] /andP[] + /eqP + _.
  have headq' : head dummy_edge [seq low i | i <- open] = bottom.
      by move: on0 headq; case: (open)=> [ // | ? ?] /=.
  rewrite headq' => pathoh.
  have : path (@edge_below R) bottom (bottom :: [seq high i | i <- open]).
      by rewrite /= edge_below_refl.
  have  := seq_low_high_shift on0 adj; rewrite headq => <-.
  rewrite -cats1 cat_path => /andP[] + _.
  rewrite ocd lceq Pab.
  by rewrite 2!map_cat 2!cat_path => /andP[]  _ /andP[] _ /= /andP[] _.
have : path (<=%R) (pvert_y p (low flc))
  [seq pvert_y p (low i) | i <- a ++ c1 :: b].
  by have := path_edge_below_pvert_y req1 req2; rewrite -map_comp.
rewrite le_path_sortedE => /andP[] /allP + _.
move=> /(_ (pvert_y p (low c1))); apply.
by apply/mapP; exists c1 => //=; rewrite !(mem_cat, inE, eqxx, orbT).
Qed.

Lemma in_new_cell_not_in_first_old e open fc cc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  s_right_form open ->
  seq_valid open (point e) ->
  out_left_event e ->
  {in cell_edges open ++ outgoing e &, no_crossing R} ->
  all open_cell_side_limit_ok open ->
  {in [seq high c | c <- fc], forall g, p_x (point e) < p_x (right_pt g)} ->
  {in fc & opening_cells (point e) (outgoing e) le he,
     forall c1 c2, o_disjoint c1 c2}.
Proof.
move=> oe cbtom adj  inbox_e rfo sval outs noc lok redges.
have ocd := decomposition_preserve_cells oe.
set result_open :=
   fc ++ opening_cells (point e) (outgoing e) le he ++ lc.
have steq : step e open nil = (result_open, closing_cells (point e) cc).
   by rewrite /step oe.
have adj' : adjacent_cells result_open.
  by have := step_keeps_adjacent inbox_e outs sval cbtom steq adj.
rewrite /opening_cells.
set new_cells := opening_cells_aux _ _ _ _.
have := l_h_in_open cbtom adj inbox_e=> -[cle [che [clein [chein ]]]].
rewrite oe /= => -[leeq heeq].
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have [/eqP ole [/eqP ohe ccn0]]:=
   l_h_c_decomposition oe (exists_cell cbtom adj inbox_e).
have nceq : opening_cells (point e) (outgoing e) le he = new_cells by [].
have [nle [nhe _]]:=
    higher_lower_equality outs oe nceq (exists_cell cbtom adj inbox_e)
         vle vhe.
have := open_not_nil (sort (@edge_below R) (outgoing e)) vle vhe.
rewrite -/new_cells => ncn0.
have [fceq | [fc' [lfc fceq]]] : fc = nil \/ exists fc' lfc, fc = rcons fc' lfc.
    by elim/last_ind : (fc) => [ | fc' lfc _];[left | right; exists fc', lfc].
  by rewrite fceq.
have lfceq : high lfc = le.
  case fc'eq : fc' => [ | init fc''].
    move: adj; rewrite ocd fceq fc'eq => /=.
    by move: ccn0 ole; case: (cc) => [ | b cc'] //= _ -> /andP[]/eqP ->.
  move: adj; rewrite ocd fceq fc'eq /= cat_path=> /andP[] _.
  rewrite last_rcons.
  by move: ccn0 ole; case: (cc) => [ | b cc'] //= _ -> /andP[]/eqP ->.
set s1 := [seq high c | c <- fc'].
set s2 := [seq high c | c <- behead new_cells ++ lc].
set g2 := high (head dummy_cell new_cells).
have roeq : [seq high c | c <- result_open] = s1 ++ [:: le, g2 & s2].
  rewrite /result_open /opening_cells map_cat fceq -cats1 map_cat -catA /=.
  congr (_ ++ (_ :: _)) => //.
  rewrite /g2 /s2 2!map_cat -/new_cells.
  by move: ncn0; case: (new_cells).
have val' : all (fun g => @valid_edge R g (point e)) (s1 ++ [:: le, g2 & s2]).
  apply/allP=> g; rewrite mem_cat=> /orP[/mapP[c cin ->] | innc].
    apply/(seq_valid_high sval)/map_f; rewrite ocd fceq mem_cat mem_rcons.
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
    by apply/(seq_valid_high sval)/map_f; rewrite ocd !mem_cat cin !orbT.
  move: cin=>/opening_cells_aux_subset=>/andP[] _.
  rewrite /= inE mem_sort=> /orP[/eqP -> //| /outs it].
  by apply: valid_edge_extremities; rewrite it.
have rfr' : sorted (@edge_below R) (s1 ++ [:: le, g2 & s2]).
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
have [lu ha] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have p'under : p' <<< g2.
  have : head dummy_cell new_cells \in new_cells by rewrite head_in_not_nil.
  move=>/opening_cells_aux_subset=> /andP[] _; rewrite -/g2 => g2in.
  rewrite (strict_under_pvert_y vg2').
  rewrite -(eqP (same_pvert_y vg2 samex)).
  apply: (lt_le_trans (_ : p_y p' < p_y (point e))).
    by rewrite [X in X < _]/= ltNge -(under_pvert_y vle).
  move: g2in; rewrite inE=> /orP[/eqP -> | ].
    by apply: ltW; rewrite -(strict_under_pvert_y vhe).
  rewrite mem_sort=>/outs/eqP lg2e.
  by rewrite -(under_pvert_y vg2) -lg2e left_pt_below.
have val'' : all (fun g => valid_edge g p') (s1 ++ [:: le, g2 & s2]).
  by apply/allP=> g gin; rewrite -(same_x_valid _ samex); apply: (allP val').
have strict_above:= edges_partition_strictly_above val'' rfr' p'above p'under.
move=> c1 c2 c1in c2in p.
apply/negP=> /andP[]/andP[] /andP[] /andP[] _ belhc1 /andP[] _ rlc1p
   /andP[] abc1l llc1p.
move=>/andP[] /andP[] /andP[] _ belhc2 /andP[] _ rlc2p /andP[] ablc2 llc2p.
have c1ok : open_cell_side_limit_ok c1.
  by apply: (allP lok); rewrite ocd !mem_cat c1in.
have leop : le \in cell_edges open by rewrite -leeq mem_cat map_f.
have heop : he \in cell_edges open by rewrite -heeq mem_cat map_f ?orbT.
have lectxt : le \in cell_edges open ++ outgoing e by rewrite mem_cat leop.
have hectxt : he \in cell_edges open ++ outgoing e by rewrite mem_cat heop.
have lebhe : le <| he.
  have [// | abs ] : below_alt le he by apply: noc.
  by move: lu; have := order_edges_viz_point' vhe vle abs (underW ha)=> ->.
have outs':
   {in sort (@edge_below R) (outgoing e), forall g, left_pt g == (point e)}.
 by move: outs; apply: sub_in1=> g; rewrite mem_sort.
have c2ok : open_cell_side_limit_ok c2.
  have noco : {in [:: le, he & outgoing e] &, no_crossing R}.
    move: noc; apply: sub_in2=> g; rewrite !inE.
    move=> /orP[/eqP -> // | /orP[/eqP -> // | gino]].
    by rewrite mem_cat gino orbT.
  have := opening_cells_side_limit vle vhe lebhe (underWC lu) ha noco outs.
  by move=> /allP/(_ c2 c2in).
move: (c1ok) => /valid_high_limits -/(_ p).
rewrite llc1p rlc1p => /(_ isT) vc1.
move: (c2ok) => /valid_low_limits -/(_ p).
rewrite llc2p rlc2p => /(_ isT) vc2.
have highc1in : high c1 \in rcons s1 le.
  move: c1in; rewrite fceq !mem_rcons !inE => /orP[/eqP -> | ].
    by rewrite lfceq eqxx.
  by move=> ?; rewrite map_f ?orbT.
have lowc2in : low c2 = le \/ low c2 \in [seq high i | i <- new_cells].
  have := opening_cells_seq_edge_shift outs' vle vhe.
  set tmp := rcons _ _.
  have /[swap] <- : low c2 \in tmp by rewrite mem_rcons inE map_f ?orbT.
  by rewrite inE -/new_cells=> /orP[/eqP -> // |];[left | right].
case: lowc2in=> [lowc2le | lowc2hnc].
  move: (belhc1); rewrite under_pvert_y // => belhc1'.
  move: ablc2; rewrite under_pvert_y // lowc2le; case/negP.
  have [/eqP c1lfc | c1nlfc] := boolP(c1 == lfc).
    by apply/(le_trans belhc1'); rewrite c1lfc lfceq lexx.
  have c1fc' : c1 \in fc'.
    by move: c1in; rewrite fceq mem_rcons inE (negbTE c1nlfc).
  have : high c1 <| le.
    have noc' : {in cell_edges open &, no_crossing R}.
    by move: noc; apply: sub_in2=> g gin; rewrite mem_cat gin.
    have := high_in_first_cells_below oe cbtom adj inbox_e sval rfo noc' redges.
    by apply; apply: map_f.
  move/edge_below_pvert_y=>/(_ _ vc1); rewrite -lowc2le vc2=> /(_ isT) c1c2.
  by apply/(le_trans belhc1').
move: (strict_above (high c1) (low c2)).
rewrite -lfceq /s1 -map_rcons -fceq map_f //.
have -> : g2 :: s2 = [seq high c | c <- new_cells ++ lc].
  by move: ncn0; rewrite /g2 /s2; case : (new_cells).
rewrite map_cat mem_cat lowc2hnc => /(_ isT isT); case/negP.
apply: (edge_below_from_point_under _ vc1 vc2) => //.
apply: noc.
  rewrite !mem_cat map_f ?orbT //.
  by rewrite ocd mem_cat c1in.
rewrite mem_cat.
have := opening_cells_aux_subset c2in=> /andP[].
by rewrite inE mem_sort => /orP[/eqP -> | -> ]; rewrite ?leop ?orbT.
Qed.

Lemma in_new_cell_not_in_last_old e open fc cc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  s_right_form open ->
  seq_valid open (point e) ->
  out_left_event e ->
  {in cell_edges open ++ outgoing e &, no_crossing R} ->
  all (edge_side_prop e) [seq high c | c <- open] ->
  all open_cell_side_limit_ok open ->
  {in opening_cells (point e) (outgoing e) le he & lc,
     forall c1 c2, o_disjoint c1 c2}.
Proof.
move=> oe cbtom adj inbox_e rfo sval outs noc aesp lok.
have ocd := decomposition_preserve_cells oe.
set new_cells := opening_cells _ _ _ _.
set result_open := fc ++ new_cells ++ lc.
have steq : step e open nil = (result_open, closing_cells (point e) cc).
   by rewrite /step oe.
have adj' : adjacent_cells result_open.
  by have := step_keeps_adjacent inbox_e outs sval cbtom steq adj.
have := l_h_in_open cbtom adj inbox_e=> -[cle [che [clein [chein ]]]].
rewrite oe /= => -[leeq heeq].
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have [/eqP ole [/eqP ohe ccn0]]:=
   l_h_c_decomposition oe (exists_cell cbtom adj inbox_e).
have [nle [nhe _]]:=
    higher_lower_equality outs oe erefl (exists_cell cbtom adj inbox_e)
         vle vhe.
have := open_not_nil (sort (@edge_below R) (outgoing e)) vle vhe.
rewrite -[X in X != [::]]/new_cells => ncn0.
move=> c1 c2 c1in c2in.
 have [s3 [s4 lceq]] := mem_seq_split c2in.
have lceq' : lc = rcons s3 c2 ++ s4 by rewrite -cats1 -catA.
have [s1 [s2 nceq']] := mem_seq_split c1in.
have hs2 : high (last c1 s2) = he.
  by move: nhe; rewrite ohe -/new_cells nceq' last_cat /=.
have lt1 : p_y (point e) < pvert_y (point e) he.
  have [_ ]:= l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  by rewrite strict_under_pvert_y.
have lc2q : last he [seq high i | i <- s3] = low c2.
  move: adj' => /adjacent_catW [] _; rewrite nceq' -catA => /adjacent_catW[] d.
  rewrite /= cat_path lceq cat_path=>/andP[] _ /andP[] _ /=.
  move=> /andP[] /eqP <- _; case: (s3) => [ // | a s'] /=.
  by rewrite last_map.
have rf' : s_right_form (last  c1 s2 :: rcons s3 c2).
(* TODO: make this one shorter. *)
  apply/allP=> c; rewrite inE=> /orP[/eqP -> {c}| cin].
    have := step_keeps_right_form cbtom adj inbox_e sval noc outs rfo.
    move=> /(_ nil result_open
             (closing_cells (point e)
       (open_cells_decomposition open (point e)).1.1.1.2)).
    rewrite /step oe; rewrite /= => /(_ erefl)/allP; apply.
    suff : {subset c1 :: s2 <= result_open} by apply; rewrite mem_last.
    move=> c cin; rewrite /result_open mem_cat orbC mem_cat nceq'.
    by rewrite mem_cat cin orbT.
  by apply: (allP rfo); rewrite ocd lceq' !mem_cat cin ?orbT.
have le2 : path <=%R (pvert_y (point e) he)
   [seq pvert_y (point e) (high i) | i <- rcons s3 c2].
  move: adj' => /adjacent_catW [] _; rewrite nceq' -catA => /adjacent_catW[] _.
  rewrite /= cat_path lceq' => /andP[] _.
  rewrite -[X in is_true X -> _]/
       (adjacent_cells ((last c1 s2 :: rcons s3 c2) ++ s4)).
  move=>/adjacent_catW[]/seq_edge_below'/(_ rf') /= => /andP[] _ + _.
  move/path_edge_below_pvert_y; rewrite hs2.
  move=> /(_ (point e)); rewrite -map_comp; apply.
  rewrite /= vhe; apply/allP=> g /mapP [c cin ->].
  by apply/(seq_valid_high sval)/map_f; rewrite ocd lceq' !mem_cat cin !orbT.
have lein : le \in cell_edges open ++ outgoing e.
  rewrite 2!mem_cat; apply/orP/or_introl/orP/or_introl; apply/mapP.
  by exists cle.
have hein : he \in cell_edges open ++ outgoing e.
  rewrite 2!mem_cat; apply/orP/or_introl/orP/or_intror; apply/mapP.
  by exists che.

have c1c2 : high c1 <| low c2.
  have /andP[_] := opening_cells_subset c1in.
  rewrite inE=> /orP[hc1he | hc1o].
  (* use that sorted edge_below lc, plus transitivity in this subset. *)
    have treblc : {in he :: [seq high i | i <- lc] & &,
                  transitive (@edge_below R)}.
      elim/last_ind : {-1} (cc) (erefl cc) ccn0 => [// | cc' ccl' _ cceq _].
(* This should be a general hypothesis of the lemma, established as an
   invariant. *)
    have all_left :{in he :: [seq high i | i <- lc], forall g,
           p_x (left_pt g) < p_x (point e)}.
      have lelow := decomposition_under_low_lc oe cbtom adj inbox_e rfo sval.
      have ccl'he : high ccl' = he by move: ohe; rewrite cceq last_rcons.
      have adjlc' : adjacent_cells (ccl' :: lc).
        move: adj; rewrite ocd cceq -cats1 -!catA /= => /adjacent_catW[] _.
        by move=> /adjacent_catW[] _ /=.
      have := seq_low_high_shift => /(_ (ccl' :: lc) isT adjlc') /= => - [] tmp.   move=> g; rewrite inE => /orP[/eqP -> | ].
    have ccl'o : ccl' \in open.
      by rewrite ocd cceq !(mem_cat, mem_rcons, inE) eqxx orbT.
    have := allP aesp (high ccl') (map_f _ ccl'o); rewrite /edge_side_prop.
    by rewrite ccl'he vhe ltNge le_eqVlt orbC lt1 /=.
    move: tmp; set s5 := rcons _ _ => tmp gin.
    have : g \in s5 by rewrite tmp inE gin orbT.
    rewrite /s5 mem_rcons inE orbC=> /orP[/mapP[c' c'in gc'] | ].
    have vc' : valid_edge (low c') (point e).
      by apply/(seq_valid_low sval)/map_f; rewrite ocd !mem_cat c'in !orbT.
    have := lelow _ c'in; rewrite strict_under_pvert_y // => ga.
    move: gin=> /mapP[c'' c''in gc''].
    have c''o : c'' \in open by rewrite ocd !mem_cat c''in !orbT.
    have := allP aesp (high c'') (map_f _ c''o); rewrite /edge_side_prop.
      rewrite (seq_valid_high sval); last by apply/map_f.
      by rewrite -gc'' gc' ltNge le_eqVlt ga orbT /=.
    move: cbtom=> /andP[] _; rewrite ocd cceq -cats1 /= !last_cat /= => /eqP ->.
move=> /eqP ->.
  by move: inbox_e=> /andP[] _ /andP[] _ /andP[] + _.
(* finished proving all_left *)
have noc' : {in he :: [seq high i | i <- lc] &, no_crossing R}.
 apply: sub_in2 noc.
  move=> g; rewrite inE => /orP[/eqP -> // | gin].
  by rewrite ocd !(mem_cat, map_cat) gin !orbT.
  have sval' : {in he :: [seq high i | i <- lc], forall g, valid_edge g (point e)}.
  move=> g; rewrite inE=> /orP[/eqP ->// | /mapP[c' c'in gc']].
  rewrite gc'; apply/(seq_valid_high sval)/map_f.
  by rewrite ocd !mem_cat c'in !orbT.
  by have := edge_below_trans (or_intror all_left) sval' noc'.

    have adj2 : adjacent_cells (last c1 s2 :: rcons s3 c2).
      move: adj'; rewrite /result_open => /adjacent_catW[] _.
      rewrite nceq' -catA /= => /adjacent_catW[] _.
      by rewrite /= cat_path lceq' cat_path => /andP[] _ /andP[] +.
      have := seq_edge_below' adj2 rf' => /= /andP[] _.
      rewrite (path_sorted_inE treblc); last first.
      apply/allP=> g; rewrite hs2 !inE => /orP[/eqP -> | ].
      by rewrite topredE inE eqxx.
rewrite topredE inE lceq' map_cat mem_cat=> ->.
by rewrite orbT.
move=> /andP[] + _ => /allP allofthem. 
have [s3nil | s3nnil] := boolP (s3 == nil).
  by rewrite (eqP hc1he) -lc2q (eqP s3nil) edge_below_refl.
move: (allofthem (last he [seq high i | i <- s3])).
   case: (s3) s3nnil lc2q => [ // | a tl] /= _; rewrite map_rcons -cats1.
   rewrite -/((_ :: _) ++ _) mem_cat mem_last=> lc2q /(_ isT).
   by rewrite lc2q hs2 (eqP hc1he).

  have : below_alt (high c1) (low c2).
    apply: noc; rewrite mem_cat; first by rewrite hc1o orbT.
    by rewrite ocd !(cell_edges_cat, mem_cat) (map_f _ c2in) !orbT.
  move/orP=>/orP[] // abs.
  have pyec2 : p_y (point e) < pvert_y (point e) (low c2).
    apply: (lt_le_trans lt1).
    case s3q : s3 => [ | a s3'].
      by move: lc2q; rewrite s3q /= => <-.
     move: le2; rewrite le_path_sortedE => /andP[] /allP le2 _.
    set w := (last (pvert_y (point e) (high a))
                  [seq pvert_y (point e) (high i) | i <- s3']).
   suff <- : w = pvert_y (point e) (low c2).
     apply: le2; rewrite map_rcons mem_rcons inE; apply/orP/or_intror.
     by rewrite /w s3q /= mem_last.
    rewrite -lc2q /= -hs2 /w s3q /= last_map.
    by apply: last_map.
  have pyec1 : p_y (point e) = pvert_y (point e) (high c1).
    apply/esym/on_pvert/out_left_event_on=> //.
  move: pyec2; rewrite pyec1 => /pvert_y_edge_below.
  have sval' := opening_valid outs vle vhe.
  rewrite (seq_valid_high sval'); last by apply/map_f.
  rewrite (seq_valid_low sval); last first.
    by apply/map_f; rewrite ocd !mem_cat c2in ?orbT.
  by rewrite abs => /(_ isT isT).
move=> p; apply/negP=> /andP[] sio1 sio2.
have lho_sub : {subset le :: he :: outgoing e <= cell_edges open ++ outgoing e}.
  move=> g; rewrite !inE =>/orP[/eqP -> // | /orP[/eqP -> // | ]].
  by rewrite mem_cat orbC => ->.
have noc' : {in le :: he :: outgoing e &, no_crossing R}.
  by apply: (sub_in2 lho_sub).
have [_ euh] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have [eal _] := l_h_above_under cbtom adj inbox_e sval oe.
have lebhe : le <| he.
  have altlh : below_alt le he by apply: noc'; rewrite !inE eqxx ?orbT.
  by apply: (edge_below_from_point_above altlh vle vhe).
have vp1 : valid_edge (high c1) p.
  apply: valid_high_limits.
    by apply: (allP (opening_cells_side_limit vle vhe lebhe eal euh noc' outs)).  by move: sio1=> /andP[] /andP[] _ /andP[] _ -> /andP[] _ ->.
have vp2 : valid_edge (low c2) p.
  apply: valid_low_limits.
    by apply: (allP lok); rewrite ocd !mem_cat c2in !orbT.
  by move: sio2 => /andP[] /andP[] _ /andP[] _ -> /andP[] _ ->.
have := edge_below_pvert_y vp1 vp2 c1c2; rewrite leNgt => /negP; apply.
have lc2p : pvert_y p (low c2) < p_y p.
  move: (sio2) => /andP[] /andP[] _ _ /andP[] + _.
  by rewrite under_pvert_y // -ltNge.
have phc1 : p_y p <= pvert_y p (high c1).
  move: sio1 => /andP[] /andP[] /andP[] _ + _ _.
  by rewrite under_pvert_y.
by apply: lt_le_trans phc1.
Qed.

Lemma step_keeps_edge_side ev open closed open' closed' events :
  step ev open closed = (open', closed') ->
  all inside_box [seq point i | i <- ev :: events] ->
  out_left_event ev ->
  s_right_form open ->
  cells_bottom_top open ->
  adjacent_cells open ->
  seq_valid open (point ev) ->
  close_edges_from_events (ev :: events) ->
  close_alive_edges open' events ->
  path (@lexPtEv _) ev events ->
  {in cell_edges open ++ outgoing ev &, no_crossing R} ->
  edge_side (ev :: events) open ->
  edge_side events open'.
Proof.
rewrite /step.
case oe: (open_cells_decomposition open (point ev)) => [[[[fc cc] lc] le] he].
move: events => [// | ev' events] [] <- _ {open' closed'}
  + outs rfo cbtom adj sval cle clae lexev noc /allP partedge.
rewrite [X in X -> _]/= => /andP[] inbox_e /andP[] inbox_e' inbox_o.
have [lec [hec [cc' [ocd [A [B [C D]]]]]]]:= lhc_dec cbtom adj inbox_e oe.
have noco :  {in cell_edges open &, no_crossing R}.
  by move: noc; apply: sub_in2=> g gin; rewrite mem_cat gin.
have lef c : c \in open -> p_x (left_pt (high c)) <= p_x (point ev).
  by move=> cino; have [] := andP (seq_valid_high sval (map_f (@high R) cino)).
have evev' : lexPt (point ev) (point ev') by case/andP: lexev.
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have /eqP  := @higher_edge_new_cells ev le  he outs _ erefl vle vhe.
set hec' := last _ _ => E.
have hec'in : hec' \in opening_cells (point ev) (outgoing ev) le he.
   have : opening_cells (point ev) (outgoing ev) le he != nil.
     by apply: open_not_nil.
  rewrite /hec'.
  by case: (opening_cells _ _ _) => [// | /= ? ? _]; rewrite mem_last.
have rpt_ev' : forall g, 
  (g \in [:: bottom; top]) || (right_pt g == point ev') -> edge_side_prop ev' g.
  move=> g /orP[gbt | gev']; rewrite /edge_side_prop.
    move: inbox_e'=> /andP[] _ /andP[] /andP[] + + /andP[]; move: gbt.
    by rewrite !inE=> /orP[] /eqP ->; case: ifP=> //; case: ifP=> //; case: ifP.
  case: ifP => [ _ | //].
  have := on_pvert (right_on_edge g); rewrite (eqP gev') => ->.
  by rewrite !lt_irreflexive.
have commondiff c : c \in hec :: fc ++ lc ->
  p_x (point ev) != p_x (point ev') -> edge_side_prop ev' (high c).
  move=> cin diffx; rewrite /edge_side_prop.
  have cino : c \in open.
    by move: cin; rewrite ocd !(inE, mem_cat) => /orP[/eqP -> | /orP[] ->];
      rewrite ?orbT // C D mem_last ?orbT.
  have : end_edge (high c) (ev' :: events).
    move: cin; rewrite inE => /orP[/eqP -> | cin]; last first.
      apply: (proj2 (andP (allP clae c _))).
      by move: cin; rewrite !mem_cat => /orP[] ->; rewrite ?orbT.
    move: (allP clae hec'); rewrite !mem_cat hec'in ?orbT.
    by move=> /(_ isT) /andP[]; rewrite B -E.
  rewrite /end_edge /event_close_edge /= orbA.
  move => /orP[rpt_easy | /hasP [ev2 ev2in /eqP rhc]].
    by apply: (rpt_ev' _ rpt_easy).
  case:ifP=> [vev' | //]; case:ifP=> [cbev' | _]; [ | case:ifP=> [caev' | // ]].
    rewrite rhc.
    have /orP[-> // | /andP[samex2 cmp2]] : lexPt (point ev') (point ev2).
      move: lexev; rewrite /= => /andP[] _; rewrite path_sortedE; last first.
        exact: lexPtEv_trans.
      by move=> /andP[] /allP /(_ ev2 ev2in).
    have := on_pvert (right_on_edge (high c)); rewrite rhc =>samey.
    have /eqP samey' := same_pvert_y vev' samex2.
    by move: cmp2; rewrite -samey -samey' ltNge le_eqVlt cbev' orbT.
  apply: (le_lt_trans (lef _ cino)).
  by move: evev'; rewrite /lexPt lt_neqAle (negbTE diffx) orbF.
apply/allP => g /mapP[c + /[dup] geq ->]; rewrite !mem_cat => /orP[];
  [ | rewrite orbC => /orP[]]; rewrite /edge_side_prop.
- move=> cfc.
  have cino : c \in open by rewrite ocd mem_cat cfc.
  have vev : valid_edge (high c) (point ev).
    by apply/(seq_valid_high sval)/map_f.
  have evafc : pvert_y (point ev) (high c) < p_y (point ev).
    have := decomposition_above_high_fc oe cbtom adj inbox_e rfo sval cfc.
    by rewrite under_pvert_y // -ltNge.
  have [samex | diffx] := boolP(p_x (point ev) == p_x (point ev')); last first.
    by apply: commondiff=> //; rewrite inE mem_cat cfc ?orbT.
  case: ifP=> [vev' | //].
  have higher : p_y (point ev) < p_y (point ev').
    move: lexev; rewrite /= /lexPtEv /lexPt => /andP[].
    by rewrite lt_neqAle samex /=.
  rewrite (le_lt_trans _ higher); last first.
    by rewrite -(eqP (same_pvert_y vev samex)) le_eqVlt evafc orbT.
  rewrite -(eqP samex).
  have := partedge (high c); rewrite /edge_side_prop map_f // vev => /(_ isT).
  by rewrite evafc.
- move=> clc.
  have cino : c \in open by rewrite ocd !mem_cat clc !orbT.
  have vev : valid_edge (high c) (point ev).
    by apply/(seq_valid_high sval)/map_f.
  have [samex | diffx] :=
         boolP(p_x (point ev) == p_x (point ev')); last first.
    by apply: commondiff => //; rewrite inE mem_cat clc !orbT.
  have yevev' : p_y (point ev) < p_y (point ev').
    move: lexev; rewrite /= /lexPtEv/lexPt lt_neqAle eq_sym=> /andP[] + _.
    by rewrite eq_sym samex.
  move: clae=> /allP/(_ c); rewrite !mem_cat clc ?orbT => /(_ isT) /andP[] _.
  rewrite /end_edge/event_close_edge /= orbA.
  move => /orP[rpt_easy | /hasP[ev2 ev2in /eqP rhc]].
    by apply: rpt_ev' rpt_easy.
  case: ifP => [vce' | //]; case: ifP => [cbev' | _]; last first.
    case: ifP => [caev' | //].
    have := partedge (high c).
    rewrite /edge_side_prop map_f ?cino // vev => /(_ isT).
    suff caev : p_y (point ev) < pvert_y (point ev) (high c).
      rewrite caev ltNge le_eqVlt caev orbT /=.
      by rewrite (eqP samex).
    by move: caev'; rewrite (eqP (same_pvert_y vev samex)); apply: lt_trans.
  rewrite rhc.
  have /orP[// | /andP[samex2 cmp2] ] : lexPt (point ev') (point ev2).
    move: lexev; rewrite /= => /andP[] _; rewrite path_sortedE; last first.
      exact: lexPtEv_trans.
    by move=> /andP[] /allP /(_ ev2 ev2in).
  have := on_pvert (right_on_edge (high c)); rewrite rhc =>samey.
  have /eqP samey' := same_pvert_y vce' samex2.
  by move: cmp2; rewrite -samey -samey' ltNge le_eqVlt cbev' orbT.
move=> /opening_cells_subset /andP[] _; rewrite inE => /orP[/eqP ishe | ].
- have heino : hec \in open by rewrite ocd C D !mem_cat mem_last !orbT.
  move: clae => /allP /(_ hec'); rewrite !mem_cat hec'in orbT.
  move=> /(_ isT) /andP[] _; rewrite E; rewrite /end_edge /event_close_edge /=.
  rewrite orbA => /orP[rpt_easy | /hasP[ev2 ev2in /eqP rhc]].
    by rewrite ishe; apply: rpt_ev' rpt_easy.
  have [_ heaev] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  move: heaev; rewrite strict_under_pvert_y // => heaev.
  have [samex | diffx] := boolP(p_x (point ev) == p_x (point ev')); last first.
    rewrite ishe -B.
    by apply: commondiff => //; rewrite inE eqxx.
  have samey := same_pvert_y vhe samex.
  case: ifP => [vce' | //].
  rewrite ishe.
  have := partedge he; rewrite -B map_f /edge_side_prop; last first.
    by rewrite ocd C D !mem_cat mem_last !orbT.
  rewrite B vhe heaev ltNge le_eqVlt heaev orbT /= (eqP samex) => /(_ isT) ->.
  have : lexPt (point ev') (point ev2).
    move: lexev; rewrite /= => /andP[] _; rewrite path_sortedE; last first.
      exact: lexPtEv_trans.
    by move=> /andP[] /allP /(_ ev2 ev2in).
  move=> /orP[ | /andP[samex2 cmp2] ].
    by rewrite rhc => -> ; case: ifP=> //; case: ifP=> //.
  have := same_pvert_y vce' samex2; rewrite ishe -(eqP samey) => /eqP ->.
  have := on_pvert (right_on_edge he); rewrite rhc => ->.
  by rewrite ltNge le_eqVlt cmp2 orbT /=.
(* last edges: from outgoing. *)
move=> ino.
move: cle => /andP[] /allP /(_ _ ino) + _.
rewrite /end_edge /event_close_edge /= orbA.
move=> /orP[rpt_easy | /hasP[ev2 ev2in /eqP rhc]].
  by apply: rpt_ev' rpt_easy.
case: ifP => [vce' | //].
case: ifP => [cbev' | _]; [ | case: ifP => [caev' | //]].
  have : lexPt (point ev') (point ev2).
    move: lexev; rewrite /= => /andP[] _; rewrite path_sortedE; last first.
      exact: lexPtEv_trans.
    by move=> /andP[] /allP /(_ ev2 ev2in).
    move=> /orP[ | /andP[samex2 cmp2] ].
      by rewrite rhc.
    have := same_pvert_y vce' samex2 => samey2.
    have := on_pvert (right_on_edge ((high c))); rewrite rhc.
    move: cbev'; rewrite (eqP samey2) => + abs; rewrite ltNge le_eqVlt.
    by rewrite abs cmp2 orbT.
have [samex | diffx] := boolP (p_x (point ev) == p_x (point ev')).
  have yevev' : p_y (point ev) < p_y (point ev').
    move: lexev; rewrite /= /lexPtEv/lexPt lt_neqAle eq_sym=> /andP[] + _.
    by rewrite eq_sym samex.
  move: caev'.
  move: (outs (high c) ino) => leftptq.
  have vev : valid_edge (high c) (point ev).
    by rewrite valid_edge_extremities // leftptq.
  have /eqP <- := same_pvert_y vev samex.
  have /on_pvert := left_on_edge (high c); rewrite (eqP leftptq) => ->.
  by move=> /ltW; rewrite leNgt yevev'.
rewrite (eqP (outs (high c) ino)).
by move: lexev => /andP[]; rewrite /lexPtEv/lexPt (negbTE diffx) orbF.
Qed.

Lemma step_keeps_disjoint_open ev open closed open' closed' events :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point ev) ->
  seq_valid open (point ev) ->
  s_right_form open ->
  {in [seq low c | c <- open] ++ [seq high c | c <- open] ++
      outgoing ev &, forall e1 e2, inter_at_ext e1 e2} ->
  {in open &, disjoint_open_cells R} ->
  out_left_event ev ->
  all open_cell_side_limit_ok open ->
  edge_side (ev :: events) open ->
  close_alive_edges open (ev :: events) ->
  all (fun x => lexPtEv ev x) events ->
  step ev open closed = (open', closed') ->
  {in open' &, disjoint_open_cells R}.
Proof.
move=> cbtom adj inbox_e sval rfo /[dup] noc /inter_at_ext_no_crossing noc'
  disj outlefte cellsok edge_side_open clae lexev.
have noc4 : {in cell_edges open ++ outgoing ev &, no_crossing R}.
   by move=> g1 g2 g1in g2in; apply: noc'; rewrite catA.
set ctxt := [seq low c | c <- open] ++ [seq high c | c <- open] ++ outgoing ev.
rewrite /step.
case oe: (open_cells_decomposition open (point ev)) => [[[[fc cc] lc] le] he].
have ocd := decomposition_preserve_cells oe.
have osub : {subset sort (@edge_below R) (outgoing ev) <= ctxt}.
  move=> g.
  have -> := perm_mem (permEl (perm_sort (@edge_below R) (outgoing ev))).
  by move=> gin; rewrite /ctxt !mem_cat gin !orbT.
have := l_h_in_open cbtom adj inbox_e.
rewrite oe /= => -[cle [che [clein [chein [/esym cleq /esym cheq]]]]].
have [eale euhe] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
set oc := opening_cells _ _ _ _.
have lein : le \in ctxt.
  by rewrite /ctxt !mem_cat cleq map_f.
have hein : he \in ctxt.
  by rewrite /ctxt !mem_cat cheq map_f ?orbT.
have vle : valid_edge le (point ev).
  by move: (seq_valid_low sval (map_f _ clein)); rewrite cleq.
have vhe : valid_edge he (point ev).
  by move: (seq_valid_high sval (map_f _ chein)); rewrite cheq.
have lowhigh : le <| he.
  have noc2 : {in [seq low c | c <- open] ++
                 [seq high c | c <- open] &, no_crossing R}.
    by move: noc'; apply: sub_in2 => g gin; rewrite catA mem_cat gin.
  by have lowhigh := open_cells_decomposition_low_under_high 
                   noc2 cbtom adj inbox_e sval rfo oe.
have outlefts :
   {in sort (@edge_below R) (outgoing ev), forall g, left_pt g == point ev}.
  move=> g.
  have -> := perm_mem (permEl (perm_sort (@edge_below R) (outgoing ev))). 
  by apply: outlefte.
have noc2 : {in le :: he :: outgoing ev &, no_crossing R}.
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
  have := decomposition_not_contain rfo sval adj cbtom inbox_e oe.
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
set fc_edges := cell_edges fc.
set lc_edges := cell_edges lc.
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
have higfc : fc != nil -> high (last dummy_cell fc) = le. (* to be used *)
  elim/last_ind : (fc) ocd adje => [// |s c' _] /= ocd + _.
  rewrite ocd cat_path last_rcons.
  by rewrite ccdec /= last_rcons lehcc => /andP[] _ /andP[] /eqP -> _. 
have lowvert : {in fc_edges, forall g, pvert_y (point ev) g < p_y (point ev)}.
  suff highs : {in [seq high c | c <- fc],
                 forall g, pvert_y (point ev) g < p_y (point ev)}.
    move=> g; rewrite mem_cat=>/orP[] gin; last by apply: highs.
    have fcn0 : fc != nil by move: gin; case: (fc).
    have : g \in rcons [seq low c| c <- fc] le.
      by rewrite mem_rcons inE gin orbT.
    have -> : le = high (last dummy_cell fc).
      move: adje; rewrite /= ocd.
      rewrite cat_path => /andP[] _.
      have -> : last dummy_cell fc = last extra_bot fc by case: (fc) fcn0.
      by rewrite lehcc ccdec => /andP[]/eqP/esym.
    rewrite seq_low_high_shift; last first.
        by move: (adj); rewrite ocd=> /adjacent_catW[].
      by apply/eqP=> abs; move: gin=>/mapP[]; rewrite abs.
    rewrite inE=> /orP[/eqP -> | ]; last by apply: highs.
    by rewrite botfc // lowbotc (pvert_y_bottom inbox_e).
  have : sorted <=%R [seq pvert_y (point ev) (high c) | c <- extra_bot::open].
    apply adjacent_right_form_sorted_le_y => //=.
      rewrite andbb; apply/andP; split=> //.
      by apply: (inside_box_valid_bottom_top inbox_e)=> //; rewrite inE eqxx.
    by rewrite edge_below_refl.
  rewrite /= => pathlt.
  move=> g /mapP[c cin gceq].
  have [s1 [s2 fceq]] := mem_seq_split cin.
  have vertle : pvert_y (point ev) le < p_y (point ev).
    have [+ _]:= l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
    rewrite under_pvert_y; last first.
      rewrite lehcc ccdec; apply/(seq_valid_low sval)/map_f.
      by rewrite ocd ccdec !mem_cat /= inE eqxx ?orbT.
    by rewrite ltNge.
  elim/last_ind : (s2) fceq => [ | s2' ls2 _] fceq.
    rewrite gceq.
    move: adje; rewrite ocd fceq /=.
    rewrite cat_path ccdec /= cats1 last_rcons => /andP[] _ /andP[] /eqP higheq.
    by rewrite higheq -lehcc => _.
  move: pathlt; rewrite ocd fceq map_cat cat_path=> /andP[] + _.
  rewrite map_cat cat_path => /andP[] _ /= => /andP[] _.
  rewrite map_rcons path_sortedE; last by apply: le_trans.
  move=>/andP[] + _ => /allP /(_ (pvert_y (point ev) (high ls2))).
  rewrite mem_rcons inE eqxx -gceq => /(_ isT) first_part.
  apply: (le_lt_trans first_part) => {first_part}.
  move: (adje);  rewrite ocd /= fceq cat_path => /andP[] _.
  rewrite -[c :: _]/([:: c] ++ _) catA -rcons_cat last_rcons ccdec /=.
  by move=> /andP[]/eqP -> _; rewrite -lehcc.
have fcopen : {subset fc <= open}.
  by move=> g gin; rewrite ocd !mem_cat gin ?orbT.
have valfc : {in fc_edges, forall g, valid_edge g (point ev)}.
  by move=> g; rewrite /fc_edges mem_cat => /orP[]/mapP[c cin ->];
    case: (andP (allP sval c _))=> //; rewrite ocd !mem_cat cin ?orbT.
(* TODO : This easy proof indicates that edge_side_prop could be made
  much easier, only the top part being important. *)
have fcedgesright: {in fc_edges, forall g, p_x (point ev) < p_x (right_pt g)}.
  move=> g; rewrite mem_cat => gin.
  have /orP[bottop | ] : end_edge g events.
      by move: gin=> /orP[] /mapP[c cin ->]; move: (allP clae' _ cin)=>/andP[].
    move: inbox_e => /andP[] _ /andP[] /andP[] _ + /andP[] _.
    by move: bottop; rewrite !inE=> /orP[] /eqP ->.
  move=> /hasP [e' e'in /eqP /[dup]geq ->].
  have : lexPt (point ev) (point e') by apply: (allP lexev).
  move=>/orP[ // | ] /andP[] /eqP xs ys.
  suff /eqP abs : pvert_y (point ev) g == p_y (point e').
    have:= lowvert g; rewrite /fc_edges mem_cat gin abs => /(_ isT).
    by rewrite ltNge le_eqVlt ys orbT.
  have vg : valid_edge g (point ev) by apply: valfc; rewrite /fc_edges mem_cat.
  have := pvert_on vg => ievg.
  move: (right_on_edge g); rewrite geq => ev'g.
  by apply: (on_edge_same_point ievg ev'g) => /=; rewrite xs eqxx.
have noc3 : {in fc_edges &, no_crossing R}.
  move: noc'; apply: sub_in2 => g.
  by rewrite ocd !map_cat !mem_cat => /orP[] ->; rewrite ?orbT /=.
have tr : {in fc_edges & &, transitive (@edge_below R)}.
  by apply: (edge_below_trans _ valfc) => //; first by left; [].

have lowfc : {in fc_edges, forall g, g <| le}.
  suff highs : {in [seq high c | c <- fc], forall g, g <| le}.
    move=> g; rewrite mem_cat=>/orP[] gin; last by apply: highs.
    have fcn0 : fc != nil by move: gin; case: (fc).
    have : g \in rcons [seq low c| c <- fc] le.
      by rewrite mem_rcons inE gin orbT.
    have -> : le = high (last dummy_cell fc).
      move: adje; rewrite /= ocd.
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
  have [fch [fct ]] := mem_seq_split cin.
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
    move: adje; rewrite /= ocd fcteq fcteq' cats0 ccdec.
    rewrite cat_cons cats1 cat_path => /andP[] _ /= => /andP[]/eqP + _.
    rewrite last_rcons geq -lehcc => ->; by rewrite edge_below_refl.
  move=> /andP[] /allP /(_ (high lf)) + _.
  rewrite -geq map_f; last by rewrite fcteq' mem_rcons inE eqxx.
  move=> /(_ isT) => ghlf.
  move: adje; rewrite /= ocd fcteq fcteq' ccdec.
  rewrite cat_cons cat_path => /andP[] _ /= => /andP[]/eqP + _.
  by rewrite last_cat last_rcons -lehcc => <-.
have ocdisjlc : {in oc & lc, forall c1 c2, o_disjoint c1 c2}.
  exact: (in_new_cell_not_in_last_old oe cbtom adj inbox_e rfo sval
     outlefte noc4 edge_side_open cellsok).
have ocdisjfc : {in oc & fc, forall c1 c2, o_disjoint c1 c2}.
  move=> c1 c2 c1in c2in p; apply/andP=> -[pino pinf].
  have := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  move=> /[dup] ib [] ibl ibh.
  move: (pino) => /andP[] /[dup] invert /andP[] inverth invertl _.
  have pxlt : {in [seq high c | c <- fc],
    forall g, p_x (point ev) < p_x (right_pt g)}.
    by move=> g gin; apply: fcedgesright; rewrite /fc_edges mem_cat gin orbT.
  have := in_new_cell_not_in_first_old oe cbtom adj inbox_e rfo sval outlefte
    noc4 cellsok pxlt.
  by move=> /(_ c2 c1 c2in c1in p); rewrite /o_disjoint pino pinf.
move=> [] <- _.
suff main : {in predU (mem oc) (mem (fc ++ lc)) &, disjoint_open_cells R}.
  by move=> c1 c2 inc1 inc2; apply: main;[move: inc1 | move: inc2];
  rewrite !(inE, mem_cat) orbCA.
apply: add_new.
- exact: o_disjointC.
- by have := opening_cells_aux_disjoint eale euhe lein hein lowhigh
              vle vhe osub noc' outlefts srt.
- move=> new old nin; rewrite mem_cat=>/orP[] oin.
    by apply: ocdisjfc.
  by apply: ocdisjlc.
move=> c1 c2 c1in c2in.
by apply: disj; rewrite ocd !mem_cat orbCA -mem_cat; apply/orP; right.
Qed.

Lemma step_keeps_disjoint ev open closed open' closed' events :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point ev) ->
  seq_valid open (point ev) ->
  s_right_form open ->
  {in [seq low c | c <- open] ++ [seq high c | c <- open] ++
      outgoing ev &, forall e1 e2, inter_at_ext e1 e2} ->
  {in open &, disjoint_open_cells R} ->
  {in closed &, @disjoint_closed_cells R} ->
  {in open & closed, @disjoint_open_closed_cells R} ->
  {in closed, forall c, right_limit c <= p_x (point ev)} ->
  out_left_event ev ->
  all open_cell_side_limit_ok open ->
  edge_side (ev :: events) open ->
  close_alive_edges open (ev :: events) ->
  all (fun x => lexPtEv ev x) events ->
  step ev open closed = (open', closed') ->
  {in closed' &, disjoint_closed_cells R} /\
  {in open' & closed', disjoint_open_closed_cells R}.
Proof.
move=> cbtom adj inbox_e sval rfo noc doc dcc docc rtl out_e sok
  edge_side_open clae lexev.
rewrite /step.
case oe : (open_cells_decomposition open (point ev)) =>
   [[[[fc  cc] lc] le] he] [<- <-].
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
    lhc_dec cbtom adj inbox_e oe.
have svalcc : seq_valid cc (point ev).
  by apply/allP=> c cin; apply: (allP sval); rewrite ocd !mem_cat cin !orbT.
have adjcc : adjacent_cells cc.
  by move: adj; rewrite ocd=>/adjacent_catW[] _ /adjacent_catW[].
have rfocc : s_right_form cc.
  by apply/allP=> c cin; apply: (allP rfo); rewrite ocd !mem_cat cin !orbT.
have allcont : all (contains_point (point ev)) cc.
  by apply/allP=> c; apply: (open_cells_decomposition_contains oe).
have closed_map : closing_cells (point ev) cc =
       [seq close_cell (point ev) c | c <- cc] by [].
have ccok : all open_cell_side_limit_ok cc.
  by apply/allP=> c cin; apply: (allP sok); rewrite ocd !mem_cat cin !orbT.
have : all (@closed_cell_side_limit_ok _) (closing_cells (point ev) cc).
  have [pal puh] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  apply: (closing_cells_side_limit' rfocc svalcc adjcc ccok allcont).
    by rewrite ccq /= leq.
  by rewrite ccq /= -heceq heq.
rewrite [X in all _ X]closed_map=> /allP cl_sok.
have oldcl_newcl :
  {in closed & closing_cells (point ev) cc, disjoint_closed_cells R}.
  move=> c1 c2 c1in.
  rewrite closed_map => /mapP[c2' c2'in c2eq].
  have c2'open : c2' \in open by rewrite ocd !mem_cat c2'in orbT.
    have vc2 : valid_cell c2' (point ev) by apply/andP/(allP sval).
  right; rewrite /c_disjoint=> q; apply/negP=> /andP[inc1 inc2].
  rewrite c2eq in inc2.
  case: (negP (docc c2' c1 c2'open _ q)) => //; rewrite inc1 andbT.
  apply:(close'_subset_contact vc2 _ inc2).
  by move: (cl_sok c2); rewrite c2eq; apply; apply: map_f.
split.
  move=> c1 c2; rewrite !mem_cat.
  move=> /orP[c1old | c1new] /orP[c2old | c2new]; first by apply: dcc.
      by apply: oldcl_newcl.
    by apply: c_disjoint_eC; apply: oldcl_newcl.
  rewrite closed_map in c1new c2new.
  move: c1new c2new => /mapP[c1' c1'in c1eq] /mapP[c2' c2'in c2eq].
  have c1'open : c1' \in open by rewrite ocd !mem_cat c1'in orbT.
  have c2'open : c2' \in open by rewrite ocd !mem_cat c2'in orbT.
  have vc1 : valid_cell c1' (point ev) by apply/andP/(allP sval).
  have vc2 : valid_cell c2' (point ev) by apply/andP/(allP sval).
  have [/eqP c1c2 | c1nc2] := boolP(c1' == c2').
    by left; rewrite c1eq c2eq c1c2.
  right=> q; apply/negP=> /andP[inc1 inc2].
  have := doc c1' c2'; rewrite ocd !mem_cat c1'in c2'in !orbT.
  move=> /(_ isT isT) [/eqP |]; first by rewrite (negbTE c1nc2).
  move=> /(_ q) /negP [].
  rewrite c1eq in inc1; rewrite c2eq in inc2.
  rewrite (close'_subset_contact vc1 _ inc1); last first.
    by apply: cl_sok; apply: map_f.
  rewrite (close'_subset_contact vc2 _ inc2) //.
  by apply: cl_sok; apply: map_f.
move=> c1 c2; rewrite !mem_cat orbCA => /orP[c1newo | c1old] c2in.
  have rlc2 : right_limit c2 <= p_x (point ev).
    move: c2in => /orP[/rtl // | ].
    rewrite closed_map=> /mapP[c2' c2'in ->].
    by rewrite close_cell_right_limit //; apply/andP/(allP svalcc).
  move=> q; rewrite inside_open'E inside_closed'E; apply/negP.
  move=> /andP[] /andP[] _ /andP[] _ /andP[] + _
     /andP[] _ /andP[] _ /andP[] _ +.
  rewrite (opening_cells_left c1newo) => evq qrlc2.
  by move: rlc2; rewrite leNgt=> /negP[]; apply (lt_le_trans evq).
have c1open : c1 \in open by rewrite ocd !mem_cat orbCA c1old orbT.
move: c2in=> /orP[c2old | ].
   apply: docc; by rewrite // ocd !mem_cat orbCA c1old orbT.
rewrite closed_map=> /mapP[c2' c2'in c2eq] q; apply/negP=> /andP[] inc1 inc2.
have c2'open : c2' \in open by rewrite ocd !mem_cat c2'in !orbT.
have [c1eqc2 | disjc1c2] := doc _ _ c1open c2'open.
  case: (decomposition_not_contain rfo sval adj cbtom inbox_e oe c1old).
  rewrite c1eqc2.
  by apply: (open_cells_decomposition_contains oe).
move: (disjc1c2 q); rewrite inc1 //.
have vc2 : valid_cell c2' (point ev) by apply/andP/(allP sval).
rewrite c2eq in inc2.
rewrite (close'_subset_contact vc2 _ inc2) //.
by apply: cl_sok; apply: map_f.
Qed.

Lemma left_limit_closing_cells (cc : seq cell) (p : pt) :
  adjacent_cells cc -> seq_valid cc p ->
  p >>> low (head_cell cc) -> p <<< high (last_cell cc) ->
  all (contains_point p) cc ->
  [seq left_limit i | i <- closing_cells p cc] = [seq left_limit i | i <- cc].
Proof.
move=> adj sval pale puhe allcont.
rewrite /closing_cells.
rewrite -map_comp; rewrite -eq_in_map /close_cell => -[] ls rs lo hi cin /=.
move: (allP sval _ cin) => /= /andP[] vlo vhi.
by rewrite (pvertE vlo) (pvertE vhi).
Qed.

Lemma step_keeps_injective_high e open closed open2 closed2 :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  s_right_form open ->
  out_left_event e ->
  uniq (outgoing e) ->
  {in open, forall c, lexPt (left_pt (high c)) (point e)} ->
  step e open closed = (open2, closed2) ->
  {in open &, injective (@high R)} ->
  {in open2 &, injective (@high R)}.
Proof.
move=> cbtom adj inbox_e sval rfo out_e uout lexp + inj_high; rewrite /step.
case oe : open_cells_decomposition => [[[[fc cc] lc] le] he].
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
have leco : lec \in open by rewrite ocd ccq !mem_cat !inE eqxx !orbT.
have heco : hec \in open by rewrite ocd ccq heceq !mem_cat mem_last !orbT.
have vle : valid_edge le (point e).
  by rewrite -leq; apply/(seq_valid_low sval)/map_f.
have vhe : valid_edge he (point e).
  by rewrite -heq; apply/(seq_valid_high sval)/map_f.
have dupcase c1 c2 : (c1 \in fc) || (c1 \in lc) ->
   c2 \in opening_cells (point e) (outgoing e) le he ->
   high c1 = high c2 -> c1 = c2.
  move=> c1in c2in hc1c2.
  have v1 : valid_edge (high c1) (point e).
    move: sval=> /allP /(_ c1); rewrite ocd !mem_cat orbCA c1in orbT.
    by move=> /(_ isT) /andP[].
  have v2 : valid_edge (high c2) (point e).
    have /andP[ _ ] := opening_cells_subset c2in.
    rewrite inE=> /orP[/eqP -> // | ].
    by have := opening_valid out_e vle vhe => /allP /(_ _ c2in) /andP[].
  have : point e <<< high c1 \/ point e >>> high c1.
    move: c1in=> /orP[] c1in.
      right.
      by have := decomposition_above_high_fc oe cbtom adj inbox_e rfo sval c1in.
    left.
    have [s1 [s2 lcq]] := mem_seq_split c1in.
    case s2q : s2 => [ | c1' s2'].
      move: inbox_e=> /andP[] /andP[] _ + _.
      suff -> : high c1 = top by [].
      by move: cbtom=> /andP[] _ /eqP; rewrite ocd lcq s2q /= !last_cat /=.
    have c1'in : c1' \in lc by rewrite lcq s2q mem_cat !inE eqxx !orbT.
    have := decomposition_under_low_lc oe cbtom adj inbox_e rfo sval c1'in.
    suff -> : high c1 = low c1' by [].
    move: adj; rewrite /adjacent_cells ocd=> /sorted_catW /andP[] _.
    move=> /sorted_catW /andP[] _; rewrite lcq s2q.
    by move=> /sorted_catW /andP[] _ /= /andP[] /eqP.
  have /andP[lows ] := opening_cells_subset c2in.
  rewrite inE => /orP[/eqP hc1he | ]; last first.
    rewrite hc1c2 => /out_e/eqP <-.
    move=> [ | ].
      rewrite strict_nonAunder; last first.
        by apply valid_edge_extremities; rewrite eqxx ?orbT.
      by rewrite left_on_edge.
    rewrite under_onVstrict ?left_on_edge //.
    by apply valid_edge_extremities; rewrite eqxx ?orbT.
  have c1hec : c1 = hec.
    apply: inj_high => //.
      by rewrite ocd !mem_cat orbCA c1in orbT.
    by rewrite hc1c2 hc1he.
  have := decomposition_not_contain rfo sval adj cbtom inbox_e oe c1in.
  have heccc : hec \in cc by rewrite ccq heceq mem_last.
  have := open_cells_decomposition_contains oe heccc.
  by rewrite c1hec => ->.
have henout : he \notin outgoing e.
  apply/negP=> /out_e /eqP abs.
  by have := lexp hec heco; rewrite heq abs lexPt_irrefl.
move=> [<- _] c1 c2; rewrite !mem_cat orbCA=> /orP[] c1in; last first.
  rewrite orbCA=> /orP[] c2in; last first.
    by apply: inj_high; rewrite ocd !mem_cat orbCA ?c1in ?c2in orbT.
  by apply: dupcase _ _ c1in c2in.
rewrite orbCA=> /orP[] c2in; last first.
  move/esym=> tmp; apply/esym; move: tmp.
  by apply: dupcase _ _ c2in c1in.
have : uniq (rcons (sort (@edge_below _) (outgoing e)) he).
  by rewrite rcons_uniq mem_sort henout sort_uniq.
by rewrite -(opening_cells_high vle vhe out_e) => /uniq_map_injective; apply.
Qed.

Lemma right_limit_close_cell p c :
  valid_edge (low c) p -> valid_edge (high c) p ->
  right_limit (close_cell p c) = p_x p.
Proof.
move=> vlc vhc; rewrite /close_cell /right_limit.
rewrite !pvertE //=.
by case: ifP; case: ifP.
Qed.

Lemma step_keeps_closed_to_the_left ev open closed open' closed' :
  cells_bottom_top open ->
  adjacent_cells open ->
  seq_valid open (point ev) ->
  inside_box (point ev) ->
  s_right_form open ->
  step ev open closed = (open', closed') ->
  {in closed, forall c, right_limit c <= p_x (point ev)} ->
  {in closed', forall c, right_limit c <= p_x (point ev)}.
Proof.
move=> cbtom adj sval inbox_e rfo.
rewrite /step.
case oe: (open_cells_decomposition open (point ev)) =>
      [[[[fc cc] lc] le] he] [_ <-].
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
have ccsub : {subset cc <= open}.
  by rewrite ocd=> c; rewrite !mem_cat orbCA=> ->.
have adjcc : adjacent_cells cc.
  by rewrite ocd in adj; move: adj => /adjacent_catW[] _ /adjacent_catW[].
have svalcc : seq_valid cc (point ev).
  by apply/allP=> c cin; apply/(allP sval)/ccsub.
have [al uh] :
  point ev >>> (low (head dummy_cell cc)) /\
  point ev <<< (high (last dummy_cell cc)).
  rewrite ccq /= -heceq leq heq.
  by apply: (l_h_above_under_strict cbtom adj inbox_e sval rfo oe).
have allcont : all (contains_point (point ev)) cc.
  by apply/allP=> c; apply: (open_cells_decomposition_contains oe).
move=> rtl c; rewrite mem_cat=> /orP[].
  by apply: rtl.
move=> /mapP[c' c'in ceq].
rewrite ceq (close_cell_right_limit) //.
by apply/andP/(allP svalcc).
Qed.

Lemma left_limit_close_cell p c : 
   left_limit (close_cell p c) = left_limit c.
Proof.
rewrite /close_cell.
by do 2 (case: (vertical_intersection_point _ _) => //).
Qed.

Lemma outgoing_high_opening s p g le he:
   valid_edge le p -> valid_edge he p ->
   {in s, forall g', left_pt g' == p} ->
   g \in s ->
   exists c, c \in opening_cells p s le he /\ high c = g.
Proof.
move=> vle vhe lefts'.
have {lefts'} lefts : {in sort (@edge_below _) s, forall g', left_pt g' == p}.
  by move=> g' g'in; apply lefts'; move: g'in; rewrite mem_sort.
rewrite -(mem_sort (@edge_below _)) /opening_cells.
elim: (sort _ _) le vle lefts => [ // | g0 s' Ih] le vle lefts.
rewrite inE=> /orP[/eqP <- /= |].
  rewrite (pvertE vle).
  eapply ex_intro; rewrite inE; split. 
    apply/orP; left; apply/eqP; reflexivity.
  by [].
move=> gin.
have : valid_edge g0 p.
  have := (@valid_edge_extremities _ g0 p).
  rewrite lefts ?eqxx //=; last by rewrite inE eqxx.
  by apply.
move=> {}/Ih [ | // | c [cin cP]].
  by move=> g' g'in; apply: lefts; rewrite inE g'in orbT.
exists c; rewrite /=. 
  by rewrite (pvertE vle) inE cin orbT cP.
Qed.

Lemma open_cells_decomposition_point_on open p fc cc lc le he c:
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box p ->
  seq_valid open p ->
  open_cells_decomposition open p = (fc, cc, lc, le, he) ->
  c \in cc -> high c != he -> p === high c.
Proof.
move=> cbtom adj inbox_p sval oe ccc nhe.
have [lec [hec [cc' [ocd [_ [hh [ccq lcc]]]]]]] :=
  lhc_dec cbtom adj inbox_p oe.
have cop : c \in open.
  by rewrite (decomposition_preserve_cells oe) !mem_cat ccc ?orbT.
have vhc : valid_edge (high c) p.
  by apply/(seq_valid_high sval)/map_f.
apply: under_above_on => //.
  by have /andP[] := open_cells_decomposition_contains oe ccc.
have [s1 [s2 cceq]] := mem_seq_split ccc.
case s2q : s2 => [ | c1 s2'].
  case/negP: nhe.
  have -> : c = hec.
    rewrite lcc -[last _ _]/(last dummy_cell (lec :: cc')) -ccq cceq s2q.
    by rewrite last_cat.
  by rewrite hh.
move: adj; rewrite ocd cceq s2q /adjacent_cells=> /sorted_catW /andP[] _.
move=> /sorted_catW /andP[] /sorted_catW /andP[] _ /andP[] /eqP hl  _ _.
have c1cc : c1 \in cc by rewrite cceq s2q mem_cat !inE eqxx !orbT.
have /andP[] := open_cells_decomposition_contains oe c1cc.
by rewrite hl.
Qed.

Lemma step_keeps_left_pt_open_lex e future_events open closed open2 closed2 :
  sorted (@lexPtEv _) (e :: future_events) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  s_right_form open ->
  out_left_event e ->
  step e open closed = (open2, closed2) ->
  {in open & (e :: future_events), forall c e',
     lexPt (left_pt (high c)) (point e')} ->
  {in open2 & future_events, forall c e',
     lexPt (left_pt (high c)) (point e')}.
Proof.
move=> sevs cbtom adj inbox_e sval rfo out_e; rewrite /step.
case oe : open_cells_decomposition => [[[[fc cc] lc] le] he].
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
move=> [<- _] lexp c e' + e'in.
have e'in2 : e' \in e :: future_events by rewrite inE e'in orbT.
rewrite !mem_cat orbCA=> /orP[]; last first.
  move=> cin; apply: lexp; last by [].
  by rewrite ocd !mem_cat orbCA cin orbT.
move=> /opening_cells_subset /andP[] _; rewrite inE => /orP[/eqP -> | ].
  rewrite -heq; apply: lexp; last by [].
  by rewrite ocd ccq !mem_cat heceq mem_last orbT.
move=> /out_e/eqP ->.
move: (sevs); rewrite /= (path_sortedE (@lexPtEv_trans _))=> /andP[] /allP + _.
by apply.
Qed.

Lemma step_keeps_open_cell_side_limit ev open closed open' closed' :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point ev) ->
  seq_valid open (point ev) ->
  out_left_event ev ->
  s_right_form open ->
  {in cell_edges open ++ outgoing ev &, no_crossing R} ->
  step ev open closed = (open', closed') ->
  all open_cell_side_limit_ok open ->
  all open_cell_side_limit_ok open'.
Proof.
move=> cbtom adj inbox_e sval out_e rfo nocs + allok; rewrite /step.
case oe : open_cells_decomposition => [[[[fc cc] lc] le] he] [] <- _.
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
apply/allP; move=> g; rewrite !mem_cat orbCA=> /orP[ | gold]; last first.
  by apply: (allP allok); rewrite ocd !mem_cat orbCA gold orbT.
move: g; apply/allP.
have [vl vh] := l_h_valid cbtom adj inbox_e sval oe.
have llh : le <| he.
  apply: open_cells_decomposition_low_under_high oe => //.
  by move=> g1 g2 g1in g2in; apply: nocs; rewrite mem_cat ?g1in ?g2in.
have [pale puhe] : point ev >>> le /\ point ev <<< he.
  by apply: l_h_above_under_strict oe.
apply: opening_cells_side_limit => //.
  by apply: underWC.
have lho_sub : {subset [::le, he & outgoing ev] <=
    cell_edges open ++ outgoing ev}.
  move=> g; rewrite 2!inE mem_cat => /orP[/eqP -> | /orP[/eqP -> | -> ]];
    last by rewrite orbT.
    by rewrite ocd mem_cat -leq map_f // ccq !mem_cat inE eqxx !orbT.
  by rewrite ocd mem_cat -heq map_f ?orbT // ccq !mem_cat heceq mem_last !orbT.
by move=> g1 g2 g1in g2in; apply: nocs; apply: lho_sub.
Qed.

Lemma step_keeps_edge_covering e open closed open2 closed2 :
(*  {in open, forall c, lexPt (left_pt (high c)) (point e)} -> *)
  all open_cell_side_limit_ok open ->
  bottom_left_cells_lex open (point e) ->
  open_non_inner_event open e ->
  {in open &, injective (@high R)} ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  s_right_form open ->
  out_left_event e ->
  forall g,
  edge_covered g open closed \/ g \in outgoing e ->
  step e open closed = (open2, closed2) ->
  edge_covered g open2 closed2.
Proof.
move=> (* lexleft *) opok btm_left
   n_inner ihigh cbtom adj inbox_e sval rfo out_e g; rewrite /step.
case oe : open_cells_decomposition => [[[[fc cc] lc] le] he].
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
have hdcclo : low (head_cell cc) = le by rewrite ccq.
have lcchi : high (last_cell cc) = he by rewrite ccq /last_cell /= -heceq.
move=> ecgVgo [] <- <- {open2 closed2}.
set new_cells := (X in fc ++ X ++ _).
set new_closed_cells := closing_cells _ _.
set open2 := (X in edge_covered _ X _).
set closed2 := (X in edge_covered _ _ X).
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have adjcc : adjacent_cells cc.
  by move: adj; rewrite ocd => /adjacent_catW [] _ /adjacent_catW[].
have svalcc : seq_valid cc (point e).
  apply/allP=> c' c'in; apply: (allP sval); rewrite ocd !mem_cat c'in.
  by rewrite orbT.
have [lu ha] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
have cont := open_cells_decomposition_contains oe.
have vlhec : valid_edge (low hec) (point e).
  have hecincc : hec \in cc by rewrite ccq heceq mem_last.
  by apply/(seq_valid_low sval)/map_f; rewrite ocd !mem_cat hecincc !orbT.
have [/eqP ghe | gnhe] := boolP(g == he).
  have gno : g \notin outgoing e.
    apply/negP=> /(out_left_event_on out_e) abs.
    have [ _ ] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
    by rewrite strict_nonAunder // -ghe abs.
  case: ecgVgo; last by rewrite (negbTE gno).
  move=> [ | [pcc [A B]]]; last first.
    right; exists pcc; split;[ | exact B].
    by rewrite /closed2; move=> g1 /A; rewrite mem_cat => ->.
  move=> [hec1 [pcc1 [subp1 [ph [cl [oo ll]]]]]].
  have hec1q : hec1 = hec.
    apply: ihigh=> //.
      by rewrite ocd !mem_cat heceq ccq mem_last !orbT.
    by rewrite heq ph // mem_rcons inE eqxx.
  left; exists (last_cell new_cells), (rcons pcc1 (last_cell new_closed_cells)).
  split.
    move=> c; rewrite /closed2 !(mem_rcons, mem_cat, inE).
    move=> /orP[/eqP -> | /subp1 -> //].
    apply/orP; right.
    by rewrite /new_closed_cells/closing_cells ccq /last_cell /= mem_last.
  split.
    move=> c; rewrite !(mem_rcons, inE) => /orP[/eqP |/orP[/eqP | inpcc1]];
        last by apply: ph; rewrite mem_rcons inE inpcc1 orbT.
      move=> ->; rewrite ghe.
      by apply/eqP; apply: (higher_edge_new_cells out_e erefl vle vhe).
    rewrite /new_closed_cells/closing_cells/last_cell ccq /= => ->.
    rewrite last_map -heceq /close_cell.
    by rewrite (pvertE vlhec) heq (pvertE vhe) /= ghe.
  split.
(* I don't know if this is used later. *)
      have last_conn : right_limit (last_cell new_closed_cells) =
                 left_limit (last_cell new_cells).
        rewrite /new_closed_cells/closing_cells/last_cell ccq.
        rewrite /= last_map -heceq /close_cell.
        rewrite (pvertE vlhec) heq (pvertE vhe) /=.
        set rl := right_limit _.
        have -> : rl = p_x (point e) by rewrite /rl; case: ifP; case: ifP=> //.
        apply/esym => {rl}.
        apply: (@opening_cells_left _ (outgoing e) le he).
        move: (opening_cells_not_nil (outgoing e) vle vhe).
        rewrite -/new_cells.
        by case: (new_cells) => [ | a l ]; rewrite //= mem_last.
(* End of fragment with unknown usage*)
    elim/last_ind : {-1} pcc1 (erefl pcc1) => [pcc1eq | pcc1' lpcc1 _ pcc1eq].
      rewrite /new_closed_cells/closing_cells/last_cell ccq /= last_map.
      rewrite /close_cell.
      set rl := right_limit _.
      have -> : rl = p_x (point e).
        rewrite /rl -heceq (pvertE vlhec) heq (pvertE vhe) /=.
        by case: ifP => [latpointe | lnotpointe];
           case: ifP => [hatpointe | hnotpointe].
      rewrite eq_sym andbT; apply/eqP.
      apply: (@opening_cells_left _ (outgoing e) le he).
      by apply/last_in_not_nil/opening_cells_not_nil.
    rewrite -pcc1eq connect_limits_rcons; last by apply/eqP/rcons_neq0.
    apply/andP; split; last first.
      rewrite last_rcons /new_closed_cells/closing_cells ccq [map _ _]/=.
      rewrite /last_cell /= last_map.
      rewrite right_limit_close_cell -?heceq // ?heq //.
      rewrite (@opening_cells_left (point e) (outgoing e) le he) //.
      by apply/last_in_not_nil/opening_cells_not_nil.
    rewrite /new_closed_cells/closing_cells ccq /last_cell /= last_map -heceq.
    move: cl; rewrite hec1q pcc1eq connect_limits_rcons; last first.
      by apply/eqP/rcons_neq0.
    rewrite (@connect_limits_rcons R (rcons _ _)); last first.
      by apply/eqP/rcons_neq0.
    move=> /andP[] -> /= /eqP ->.
    by rewrite left_limit_close_cell eqxx.
  split.
    rewrite /open2 !mem_cat last_in_not_nil ?orbT //.
    by apply: opening_cells_not_nil.
  move: ll.
  case pcc1q: pcc1 => [ | pcc0 pcc1']; last by [].
  rewrite /head_cell/new_closed_cells/closing_cells/last_cell ccq /=.
  by rewrite last_map -heceq left_limit_close_cell hec1q.
case: ecgVgo=> [ecg |go ]; last first.
  left.
  case: (outgoing_high_opening vle vhe out_e go) => [c [cin cP]].
  exists c, [::]; rewrite /=; split.
    by move=> x xin.
  split; first by move=> c'; rewrite inE => /eqP->.
  split; first by [].
  split; first by rewrite /open2 /new_cells !mem_cat cin ?orbT.
  rewrite (opening_cells_left cin); apply/esym/eqP.
  by rewrite (eqP (out_e g go)) eqxx.
case: ecg => [| [pcc [subcl All_other]]]; last first.
  right; exists pcc; split;[ | exact All_other].
  by move=> c cin; rewrite /closed2 mem_cat subcl.
move=> [opc [pcc [subcl [highs [conn [/[dup] opcopen + leftl]]]]]].
rewrite ocd; rewrite !mem_cat orbCA => /orP[]; last first.
  move=> inO.
  left; exists opc, pcc.
  split; first by move=> c cin; rewrite /closed2 mem_cat subcl.
  split; first by [].
  split; first by [].
  split; first by rewrite /open2 /new_cells !mem_cat orbCA inO orbT.
  by [].
move=> opcc.
right.
have [_ highopc leftopc]:= close_cell_preserve_3sides (point e) opc.
exists (rcons pcc (close_cell (point e) opc)).
split.
  move=> c; rewrite mem_rcons inE=> /orP[/eqP -> | ].
    rewrite /closed2 mem_cat/new_closed_cells/closing_cells; apply/orP; right.
    by apply/mapP; exists opc.
  by move=> cin; rewrite /closed2 mem_cat subcl.
split.
  move=> c; rewrite mem_rcons inE => /orP[/eqP -> | inpcc]; last first.
    by apply highs; rewrite mem_rcons inE inpcc orbT.
  by rewrite highopc; apply highs; rewrite mem_rcons inE eqxx.
split.
  have [/eqP -> | pccn0] := boolP (pcc == [::]).
    by [].
  move: conn; rewrite !connect_limits_rcons // => /andP[] -> /eqP -> /=.
  by rewrite /left_limit leftopc.
split.
  move: leftl; case pccq: pcc => [ | pcc0 pcc'] //=.
  by rewrite /left_limit leftopc.
rewrite /last_cell last_rcons right_limit_close_cell; last first.
    by apply/(seq_valid_high sval)/map_f.
  by apply/(seq_valid_low sval)/map_f.
have hopc : high opc = g by apply: highs; rewrite mem_rcons inE eqxx.
have e_on : point e === high opc.
  apply: (open_cells_decomposition_point_on cbtom adj inbox_e sval oe opcc).
  by rewrite hopc.
have [ abs | -> ] := n_inner _ opcopen e_on; last by rewrite hopc.
have := bottom_left_lex_to_high cbtom adj rfo opok inbox_e btm_left opcopen.
by rewrite abs lexPt_irrefl.
Qed.

Lemma step_keeps_subset open closed open' closed' ev :
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point ev) ->
  step ev open closed = (open', closed') ->
  {subset cell_edges open' <= cell_edges open ++ outgoing ev}.
Proof.
move=> cbtom adj inbox_e.
rewrite /step.
case oe : (open_cells_decomposition open (point ev)) =>
  [[[[fc cc] lc] le] he] [] <- _.
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_e oe.
move=> g; rewrite ocd !cell_edges_cat mem_cat cell_edges_cat.
rewrite  [X in _ || X]mem_cat orbCA=> /orP[ | gold]; last first.
  rewrite /all_edges mem_cat cell_edges_cat mem_cat cell_edges_cat.
  by rewrite [X in _ || X || _]mem_cat orbCA gold !orbT.
rewrite mem_cat=> /orP[] /mapP [] c cin gq.
  have gle_or_out : g = le \/ g \in outgoing ev.
    have:= opening_cells_subset cin; rewrite -gq inE=> /andP[]/orP[/eqP| ] ->;
    by auto.
  move: gle_or_out => [-> | ].
    by rewrite !mem_cat ccq -leq map_f // !mem_cat inE eqxx !orbT.
  by rewrite /all_edges mem_cat orbC /events_to_edges /= mem_cat=> ->.
have ghe_or_out : g = he \/ g \in outgoing ev.
  have:= opening_cells_subset cin.
   by rewrite -gq andbC inE=> /andP[]/orP[/eqP|]->; auto.
move: ghe_or_out => [-> | ].
  rewrite !mem_cat ccq -heq map_f ?orbT //.
  by rewrite heceq !mem_cat mem_last !orbT.
by rewrite /all_edges mem_cat orbC /events_to_edges /= mem_cat=> ->.
Qed.

Lemma above_point_in_closing open p q fc cc lc le he:
   cells_bottom_top open -> adjacent_cells open -> inside_box p ->
   seq_valid open p -> s_right_form open ->
   {in open, forall c, left_limit c <= p_x p} ->
   open_cells_decomposition open p = (fc , cc, lc, le, he) ->
   p_x q = p_x p -> p_y p < p_y q -> q <<= he ->
   inside_closed' q (last dummy_cell (closing_cells p cc)) ||
   ~~has (inside_open' q) open.
Proof.
move=> cbtom adj inbox_p sval rfo llim oe samex above under.
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
  lhc_dec cbtom adj inbox_p oe.
have adjcc : adjacent_cells (lec :: cc').
  by move: adj; rewrite ocd ccq=> /adjacent_catW[] _ /adjacent_catW[] + _.
have valcc : seq_valid (lec :: cc') p.
  by apply/allP=> x xin; apply: (allP sval); rewrite ocd !mem_cat ccq xin !orbT.
have vhe : valid_edge he p.
  by apply: (seq_valid_high valcc); rewrite -heq map_f // heceq mem_last.
have vhep : valid_edge (high hec) p by rewrite heq.
have /allP cont := open_cells_decomposition_contains oe.
rewrite ccq in cont.
have [pal puh] := l_h_above_under_strict cbtom adj inbox_p sval rfo oe.
rewrite ccq closing_cells_single_map.
have vlep : valid_edge (low hec) p.
  apply: (seq_valid_low sval); rewrite ocd ccq; apply: map_f.
  by rewrite !mem_cat heceq mem_last orbT.
have trp : forall g, valid_edge g p -> valid_edge g q.
  by move=> g; rewrite /valid_edge samex.
rewrite inside_closed'E /= last_map -heceq.
rewrite left_limit_close_cell right_limit_close_cell //.
have : left_limit hec <= p_x q.
  by rewrite samex; apply: llim; rewrite ocd ccq heceq !mem_cat mem_last orbT.
have vle : valid_edge le p.
  by apply: (seq_valid_low valcc); rewrite -leq map_f // inE eqxx.
have vleq : valid_edge le q by apply/trp.
have samex' : p_x q == p_x p by apply/eqP.
have samex'' : p_x p == p_x q by apply/eqP.
have vlhq : valid_edge (low hec) q by apply/trp.
have qal : q >>> low hec.
  have [/eqP cc'0 | cc'n0] := boolP(cc' == [::]).
    rewrite heceq cc'0 /= leq under_pvert_y // -ltNge (lt_trans _ above) //.
    rewrite (eqP (same_pvert_y vleq samex')).
    by move: pal; rewrite under_pvert_y // -ltNge.
  have /andP[+ _] : contains_point p hec.
    by apply: (allP cont); rewrite heceq mem_last.
  rewrite strict_under_pvert_y // -leNgt.
  rewrite -(eqP (same_pvert_y vlhq samex'))=> /le_lt_trans /(_ above).
  by rewrite ltNge -under_pvert_y.
rewrite le_eqVlt=> /orP[/eqP hec0 | ->]; last first.
  rewrite samex le_refl /close_cell (pvertE vhep) (pvertE vlep) /=.
  by rewrite heq under qal.
apply/orP; right; apply/negP=> /hasP[c /[dup] cin + qinc].
have vcp : valid_edge (low c) p /\ valid_edge (high c) p.
  by apply/andP; apply: (allP sval).
have [vlq vhq] : valid_edge (low c) q /\ valid_edge (high c) q.
  by move: vcp=> [] /trp + /trp.
move: vcp=> [vlp vhp].
have hdo : head dummy_edge [seq low i | i <- open] = bottom.
    by move: cbtom => /andP[]; case: (open)=> [ // | a l] /= /eqP ->.
have := seq_edge_below' adj rfo; rewrite hdo ocd !map_cat !cat_path => patheb.
rewrite !mem_cat orbCA => /orP[cincc | cold]; last first.
  move: cold=> /orP[] /[dup] cold /mem_seq_split [s1 [s2 s1s2q]].
    have := decomposition_above_high_fc oe cbtom adj inbox_p rfo sval cold.
    rewrite under_pvert_y // -ltNge.
    move: qinc; rewrite inside_open'E => /andP[] + _.
    rewrite under_pvert_y //; rewrite -(eqP (same_pvert_y vhp _)) //.
    move=> /le_lt_trans it; move=> {}/it /(lt_trans above).
    by rewrite lt_irreflexive.
  have : all (fun g => valid_edge g p) (he :: [seq high i | i <- lc]).
    rewrite /= -heq (seq_valid_high valcc) ?andTb; last first.
      by rewrite map_f // heceq mem_last.
    apply/allP=> x /mapP [xc xcin xeq]; apply: (seq_valid_high sval).
    by apply/mapP; exists xc=> //; rewrite ocd !mem_cat xcin !orbT.
  move=> /path_edge_below_pvert_y convert.
  move:(patheb)=> /andP[] _ /andP[] _; rewrite ccq /= last_map -heceq heq.
  move=> {}/convert; rewrite le_path_sortedE => /andP[] abovehe _.
  move: adj; rewrite ocd ccq=> /adjacent_catW [] _ /=.
  rewrite cat_path => /andP[] _; rewrite s1s2q cat_path => /andP[] _ /= /andP[].
  move=> /eqP/esym lcq _.
  move: qinc; rewrite inside_open'E => /andP[] _ /andP[] + _.
  rewrite under_pvert_y // lcq.
  have vheq : valid_edge he q by apply: trp.
  case s1q : s1 => [ | c0 s1'].
    by rewrite /= -heceq heq -under_pvert_y ?under.
  have vlp' : valid_edge (high (last c0 s1')) p.
    by move: lcq; rewrite s1q /= => <-.
  rewrite /= -ltNge -(eqP (same_pvert_y vlp' _))=> [ql | ]; last first.
    by apply/eqP.
  have : last c0 s1' \in lc by rewrite s1s2q s1q mem_cat mem_last.
  move=> /(map_f (@high R)) /(map_f (pvert_y p)) m.
  have hel := (allP abovehe _ m).
  move: under; rewrite under_pvert_y // leNgt -(eqP (same_pvert_y vhe _)) //.
  by rewrite (le_lt_trans hel ql).
have cnhec : c <> hec.
  by move: qinc=> /[swap] ->; rewrite inside_open'E hec0 lt_irreflexive ?andbF.
have [cc1 cc1p] : exists cc1, cc = cc1 ++ [:: hec].
  elim/last_ind: (cc) ccq => [// | cc1 b _] it.
  exists cc1; rewrite cats1 heceq; congr (rcons _ _).
  by rewrite -[b](last_rcons b cc1) it.
move: cincc; rewrite cc1p mem_cat inE=> /orP[ | /eqP abs]; last by case: cnhec.
move=> /mem_seq_split [s1 [s2 s1s2q]].
have /path_edge_below_pvert_y convert : all (fun g => valid_edge g p)
   (last bottom [seq high i | i <- fc] :: [seq high i | i <- cc]).
    rewrite /=; apply/andP; split; last first.
    by apply/allP=> x xin; apply: (seq_valid_high valcc); rewrite -ccq.
  case fcq : fc => [/= | c0 fc1].
    by apply: (inside_box_valid_bottom_top inbox_p)=> //; rewrite inE eqxx.
  rewrite /= last_map; apply: (seq_valid_high sval).
  by rewrite ocd fcq map_cat mem_cat map_f // mem_last.
move: patheb => /andP[] _ /andP[] /convert +  _.
rewrite cc1p s1s2q -catA /= !map_cat cat_path=> /andP[] _ /= /andP[] _.
rewrite le_path_sortedE=> /andP[] cmpchec _.
move: (adjcc); rewrite -ccq cc1p s1s2q -catA=> /adjacent_catW[] _ /=.
rewrite cat_path=>/andP[] _ ls2.
have cmp' : pvert_y p (high c) <= pvert_y p (low hec).
  case s2q : s2 => [ | c1 s2'].
    by move: ls2; rewrite s2q /= andbT => /eqP ->.
  have tin : pvert_y p (high (last c1 s2')) \in
             [seq pvert_y p g | g <- [seq high i | i <- s2 ++ [:: hec]]].
    by rewrite map_f // map_f // mem_cat s2q mem_last.
  move: (allP cmpchec _ tin).
  by move: ls2; rewrite s2q /= andbT=> /eqP ->.
move: qinc; rewrite inside_open'E=> /andP[] + _ .
rewrite under_pvert_y // -(eqP (same_pvert_y vhp _)) // => cmp2.
have := le_trans cmp2 cmp'.
move: qal; rewrite under_pvert_y // -(eqP (same_pvert_y vlep _)) //.
by move=> /negbTE ->.
Qed.

Lemma step_keeps_cover_left_border e open closed open' closed' evs :
  (*sorted (@lexPt R) [seq point x | x <- (e :: evs)] -> *)
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  out_left_event e ->
  s_right_form open ->
  close_alive_edges open (e :: evs) ->
  close_edges_from_events (e :: evs) ->
  {in cell_edges open ++ flatten [seq outgoing i | i <- e :: evs] &,
     no_crossing R} ->
  bottom_left_cells_lex open (point e) ->
  step e open closed = (open', closed') ->
  {in open, forall c p, inside_box p -> left_limit c = p_x p ->
    contains_point' p c -> has (inside_closed' p) closed} ->
  {in open', forall c p, inside_box p -> left_limit c = p_x p ->
    contains_point' p c -> has (inside_closed' p) closed'}.
Proof.
move=> (*sortevs*) cbtom adj inbox_e sval oute rfo clae clev noc btm_left stepeq.
have := step_keeps_bottom_top inbox_e sval adj cbtom oute stepeq.
have := step_keeps_adjacent inbox_e oute sval cbtom stepeq adj.
have := step_keeps_left_pts_inf' inbox_e oute rfo sval adj cbtom clae
  clev noc btm_left stepeq.
have := step_keeps_closeness inbox_e oute rfo cbtom adj sval clev clae
   stepeq.
have :=
   step_keeps_valid _ inbox_e _ oute rfo cbtom adj sval clae clev _ stepeq.
have noc' : {in cell_edges open ++ outgoing e &, no_crossing R}.
  by move=> g1 g2 g1in g2in; apply: noc; rewrite /= !mem_cat orbA
   -2!mem_cat ?g1in ?g2in.
have rfo' := step_keeps_right_form cbtom adj inbox_e sval noc' oute rfo stepeq.
move: stepeq; rewrite /step /=.
case oe : (open_cells_decomposition open (point e)) => [[[[fc cc] lc] le] he].
move=> [] /esym openeq /esym closeeq.
move=> sval0' clae' btm_left' adj' cbtom' left_border c cin p inboxp lbnd pin.
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
    lhc_dec cbtom adj inbox_e oe.
move: cin; rewrite openeq !mem_cat orbCA orbC=> /orP[cold | cnew].
  rewrite closeeq has_cat; apply/orP; left.
  apply: (left_border c _ _ inboxp lbnd pin).
  by rewrite ocd !mem_cat orbCA cold orbT.
have ppe : p_x p = p_x (point e).
  by rewrite -lbnd (opening_cells_left cnew).
have adjcc : adjacent_cells cc.
  by move: adj; rewrite ocd=> /adjacent_catW[] _ /adjacent_catW[].
have valcc : seq_valid cc (point e).
  by apply/allP=> x xin; apply: (allP sval); rewrite ocd !mem_cat xin ?orbT.
have [ea eu] : point e >>> low (head dummy_cell cc) /\
          point e <<< high (last dummy_cell cc).
  rewrite ccq /= leq -heceq heq.
  apply: (l_h_above_under_strict cbtom adj inbox_e sval rfo oe).
have allcont : all (contains_point (point e)) cc.
  by apply/allP=> x xin; apply: (open_cells_decomposition_contains oe).
have [vle vhe] := l_h_valid cbtom adj inbox_e sval oe.
have /andP [vlep vhep] : valid_edge le p && valid_edge he p.
  by move: vle vhe; rewrite /valid_edge ppe=> -> ->.
have lonew : low (head dummy_cell
                 (opening_cells (point e) (outgoing e) le he)) = le.
  by have := lower_edge_new_cells erefl vle vhe => /eqP.
have lonew' : head dummy_edge
    [seq low c | c <- opening_cells (point e) (outgoing e) le he] = le.
  move: (opening_cells_not_nil (outgoing e) vle vhe) lonew.
  by set w := opening_cells _ _ _ _; case: w=> [ | a tl].
have highnew : [seq high i | i <- opening_cells (point e)(outgoing e) le he]=
               rcons (sort (@edge_below _) (outgoing e)) he.
  by rewrite (opening_cells_high vle vhe).
have allval : all (fun g => valid_edge g p) 
     (head dummy_edge [seq low i | i <- opening_cells (point e) 
              (outgoing e) le he] ::
     [seq high i | i <- opening_cells (point e) (outgoing e) le he]).
  apply/allP=> x; rewrite inE=> xin.
  suff : valid_edge x (point e) by rewrite /valid_edge ppe.
  move: xin=> /orP[/eqP xin | xin]; first by rewrite xin lonew'.
  rewrite (opening_cells_high vle vhe) // ?mem_rcons inE mem_sort in xin.
  case/orP: xin=> [/eqP -> // | xin ].
  apply: valid_edge_extremities; apply/orP; left.
  by apply: oute.
have lecc : lec \in cc by rewrite ccq inE eqxx.
have lecin : lec \in open.
  by rewrite ocd !mem_cat lecc orbT.
have vhlece : valid_edge (high lec) (point e).
  by have := seq_valid_high sval (map_f (@high R) lecin).
have vhlecp : valid_edge (high lec) p.
  by move: vhlece; rewrite /valid_edge ppe.        
move: adj'; rewrite openeq=> /adjacent_catW[] _ /adjacent_catW[] adjo _.
have [yle | yabove] := lerP (p_y p) (p_y (point e)).
  have pale : p >>> le.
    have /mem_seq_split [s1 [s2 s1s2q]] := cnew.
    case s1q : s1 => [ | c0 s1'].
      by move: lonew; rewrite s1s2q s1q /= => <-; move: pin=> /andP[].
    have lco : low c \in outgoing e.
      have := seq_low_high_shift (opening_cells_not_nil (outgoing e) vle vhe)
                adjo.
      rewrite s1s2q s1q /= => - [].
      rewrite -[RHS]/[seq high i | i <- (c0 :: s1') ++ c :: s2] -s1q -s1s2q.
      rewrite opening_cells_high // => /rcons_inj [] lows _.
      have : low c \in [seq low i | i <- s1' ++ c :: s2].
        by apply: map_f; rewrite mem_cat inE eqxx orbT.
      by rewrite lows mem_sort.
    have vlce : valid_edge (low c) (point e).
      by apply: valid_edge_extremities; rewrite (oute (low c)).
    move: pin => /andP[] + _; rewrite under_pvert_y; last first.
      by move: vlce; rewrite /valid_edge ppe.
    rewrite -(eqP (same_pvert_y vlce _)); last by apply/eqP.
    by rewrite on_pvert ?yle // -(eqP (oute (low c) _)) // left_on_edge.
  have plec : contains_point' p lec.
    rewrite /contains_point' leq pale /=.
    rewrite under_pvert_y  //.
    apply: (le_trans yle); rewrite -(eqP (same_pvert_y vhlece _)); last first.
      by apply/eqP.
    rewrite -under_pvert_y //.
    have/(open_cells_decomposition_contains oe)/andP[]// : lec \in cc.
    by rewrite ccq inE eqxx.
  have [/eqP lbnd' | safe] := boolP(left_limit lec == p_x p).
    rewrite closeeq has_cat.
    by rewrite (left_border _ lecin).
  have lbnd2 : left_limit lec < p_x p.
    rewrite lt_neqAle safe /=.
    rewrite ppe; apply/lexePt_xW/lexPtW.
    by apply: (btm_left lec lecin).
  rewrite closeeq has_cat; apply/orP; right.
  apply/hasP; exists (close_cell (point e) lec).
    by apply:map_f; rewrite ccq inE eqxx.
  have vlec : valid_cell lec (point e).
    by apply/andP; apply: (allP valcc); rewrite ccq inE eqxx.
  rewrite inside_closed'E /left_limit.
  have [-> -> ->]:= close_cell_preserve_3sides (point e) lec.
  move: plec=> /andP[] -> ->.
  by rewrite (close_cell_right_limit) // lbnd2 ppe lexx.
have phec : contains_point' p hec.
  have puhe : p <<= he.
    have /mem_seq_split [s1 [s2 s1s2q]] := cnew.
    elim /last_ind: {2} (s2) (erefl s2) => [ | s2' c2 _] s2q.
      move: highnew; rewrite s1s2q s2q /= map_cat /= cats1=> /rcons_inj[] _ <-.
      by move: pin => /andP[].
    have hco : high c \in outgoing e.
      have := opening_cells_high vle vhe oute; rewrite s1s2q s2q.
      rewrite (_ : [seq high i | i <- s1 ++ c :: rcons s2' c2] =
             rcons [seq high i | i <- s1 ++ c :: s2'] (high c2)); last first.
        by rewrite !map_cat /= map_rcons -!cats1 /= -!catA /=.
      move=> /rcons_inj[] his _.
      have : high c \in [seq high i | i <- s1 ++ c :: s2'].
        by apply: map_f; rewrite mem_cat inE eqxx orbT.
      by rewrite his mem_sort.
    have vhce : valid_edge (high c) (point e).
      by apply: valid_edge_extremities; rewrite (oute (high c)).
    move: (pin) => /andP[] _; rewrite under_pvert_y; last first.
      by move: vhce; rewrite /valid_edge ppe.
    rewrite -(eqP (same_pvert_y vhce _)); last by apply/eqP.
    rewrite on_pvert; last first.
      by rewrite -(eqP (oute (high c) _)) // left_on_edge.
    move=> ple.
    have ppe': p_y p = p_y (point e).
      by apply: le_anti; rewrite ple (ltW yabove).
    have/eqP -> : p == point e by rewrite pt_eqE ppe ppe' !eqxx.
    by apply/underW; move: eu; rewrite ccq /= -heceq heq.
  rewrite /contains_point'; rewrite heq puhe andbT.
  have vlhece : valid_edge (low hec) (point e).
    apply: (seq_valid_low valcc); apply/map_f.
    by rewrite ccq heceq mem_last.
  have vlhecp : valid_edge (low hec) p.
    by move: vlhece; rewrite /valid_edge ppe.
  rewrite under_pvert_y // -?ltNge.
  apply: le_lt_trans yabove.  
  rewrite -(eqP (same_pvert_y vlhece _)); last by apply/eqP.
  rewrite leNgt -strict_under_pvert_y //.
  have/(open_cells_decomposition_contains oe)/andP[]// : hec \in cc.
    by rewrite ccq heceq mem_last.
have hecin : hec \in open.
    by rewrite ocd ccq !mem_cat heceq mem_last !orbT.
have [/eqP lbnd' | safe] := boolP(left_limit hec == p_x p).
  rewrite closeeq has_cat.
  by have -> := left_border _ hecin _ _ lbnd' phec.
have lbnd2 : left_limit hec < p_x p.
  rewrite lt_neqAle safe /=.
  rewrite ppe; apply/lexePt_xW/lexPtW.
  by apply: (btm_left hec hecin).
rewrite closeeq has_cat; apply/orP; right.
apply/hasP; exists (close_cell (point e) hec).
  by apply: map_f; rewrite ccq heceq mem_last.
have vhec : valid_cell hec (point e).
  by apply/andP; apply: (allP valcc); rewrite ccq heceq mem_last.
rewrite inside_closed'E /left_limit.
have [-> -> ->]:= close_cell_preserve_3sides (point e) hec.
move: phec=> /andP[] -> ->.
by rewrite (close_cell_right_limit) // lbnd2 ppe lexx.
Qed.

Lemma step_keeps_cover e open closed open' closed' p evs :
  sorted (@lexPt R) [seq point x | x <- (e :: evs)] ->
  cells_bottom_top open ->
  adjacent_cells open ->
  inside_box (point e) ->
  seq_valid open (point e) ->
  out_left_event e ->
  s_right_form open ->
  close_alive_edges open (e :: evs) ->
  close_edges_from_events (e :: evs) ->
  {in cell_edges open ++ flatten [seq outgoing i | i <- e :: evs] &,
     no_crossing R} ->
  bottom_left_cells_lex open (point e) ->
  {in open, forall c p, inside_box p -> left_limit c = p_x p ->
    contains_point' p c -> has (inside_closed' p) closed} ->
  step e open closed = (open', closed') ->
  cover_left_of (point e) open closed ->
  all (lexePt p) [seq point e | e <- evs] ->
  cover_left_of p open' closed'.
Proof.
move=> sortevs cbtom adj inbox_e sval oute rfo clae clev noc btm_left 
  left_border_in stepeq.
have cbtom' := step_keeps_bottom_top inbox_e sval adj cbtom oute stepeq.
have adj' := step_keeps_adjacent inbox_e oute sval cbtom stepeq adj.
have := step_keeps_left_pts_inf' inbox_e oute rfo sval adj cbtom clae
  clev noc btm_left stepeq.
have := step_keeps_closeness inbox_e oute rfo cbtom adj sval clev clae
   stepeq.
have :=
   step_keeps_valid _ inbox_e _ oute rfo cbtom adj sval clae clev _ stepeq.
have := step_keeps_cover_left_border cbtom adj inbox_e sval oute rfo clae clev
  noc btm_left stepeq left_border_in.
move: stepeq; rewrite /step /=.
case oe : (open_cells_decomposition open (point e)) => [[[[fc cc] lc] le] he].
have subcc : {subset cc <= open}.
  by move=> x xin; rewrite (decomposition_preserve_cells oe) !mem_cat xin orbT.
move=> [] open'eq closed'eq left_border_in' 
  sval0' clae' btm_left' cov limr q inbox_q limrq.
have [lec [hec [cc' [ocd [leq [heq [ccq heceq]]]]]]] :=
   lhc_dec cbtom adj inbox_e oe.
have [qright | qleft] := boolP(lexPt (point e) q).
  have [c cin ctn]:= exists_cell cbtom' adj' inbox_q.
  have subpq1 : subpred (lexePt p) (lexePt q).
    by move=> x px; apply/(lexePt_trans limrq).
  have limrq1 := sub_all subpq1 limr.
  have limrq' : forall e, e \in evs -> lexePt q (point e).
    by move/(sub_all subpq1): (limr); rewrite all_map=>/allP.
  have sval' := sval0' _ inbox_q qright limrq'.
  move: cin; rewrite -open'eq !mem_cat orbCA -mem_cat => /orP[] cin; last first.
    have [inc | ninc] := boolP(inside_open' q c).
      rewrite 2!has_cat orbCA -has_cat; apply/orP; left; apply/orP; right.
      by apply/hasP; exists c.
    have cin0 : c \in open by rewrite ocd !mem_cat orbCA -mem_cat cin ?orbT.
    have cin1 : c \in open'.
      by rewrite -open'eq !mem_cat orbCA -mem_cat cin orbT.
    apply/orP; right.
    rewrite -closed'eq has_cat; apply/orP; left.
    move: ninc; rewrite inside_open'E; rewrite lt_neqAle.
    move: (ctn)=> /andP[] -> -> /=.
    have -> : left_limit c <= p_x q.
      have : p_x (point e) <= p_x q by apply/lexePt_xW/lexPtW.
      apply: le_trans.
      rewrite /left_limit -[X in X <= _]/(p_x (bottom_left_corner c)).
      by apply/lexePt_xW/lexPtW; apply: btm_left.
    have -> : p_x q <= open_limit c.
      rewrite /open_limit le_minr.
      have extg : forall g, g \in [:: bottom; top] -> p_x q <= p_x (right_pt g).
        move: inbox_q=> /andP[] _ /andP[] /andP[] _ /ltW + /andP[] _ /ltW.
        by move=> A B g; rewrite !inE=> /orP[] /eqP ->.
      have intg g : has (event_close_edge g) evs -> p_x q <= p_x (right_pt g).
        move=>/hasP[] ev' ev'in /eqP ->.
        by apply/lexePt_xW/(lexePt_trans limrq)/(allP limr)/map_f.
      move: clae' => /allP /(_ _ cin1) /andP[].
      by move=> /orP[/extg | /intg] -> /orP[/extg | /intg] ->.
    rewrite !andbT negbK => /eqP atll.
    by apply: (left_border_in _ cin0 _ inbox_q atll ctn).
  have [vertp | rightofp] : left_limit c = p_x q \/ left_limit c < p_x q.
      rewrite (opening_cells_left cin).
      move: qright=> /lexPtW/lexePt_xW; rewrite le_eqVlt=> /orP[/eqP -> | ->].
        by left.
      by right.
    rewrite (left_border_in' _ _ _ _ vertp ctn) ?orbT //.
    by rewrite -open'eq !mem_cat cin orbT.
  rewrite !has_cat; apply /orP; left; apply/orP; right; apply/orP; left.
  apply/hasP; exists c=> //.
  rewrite inside_open'E rightofp /open_limit le_minr.
  have [/andP[_ ->] /andP[_ ->]] : valid_cell c q.
    by apply/andP; apply: (allP sval'); rewrite -open'eq !mem_cat cin ?orbT.
  by move: ctn=> /andP[] -> ->.
have qe : p_x q <= p_x (point e).
  by apply: lexePt_xW; rewrite lexePtNgt.
have inclosing : forall c, c \in cc -> inside_open' q c ->
  (forall c, c \in cc -> valid_edge (low c) (point e) &&
     (valid_edge (high c) (point e))) ->
  exists2 c', c' \in closing_cells (point e) cc & inside_closed' q c'.
  move=> c cin ins allval.
  have /allP ctps : forall c, c \in cc -> contains_point (point e) c.
    by move=> ?; apply: (open_cells_decomposition_contains oe).
  have [/eqP/esym lel [/eqP/esym heh _]] :=
     l_h_c_decomposition oe (exists_cell cbtom adj (inbox_e)).
  have [eabovel ebelowh] :=
        l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
  have ccsub : {subset cc <= open}.
    by move=> x xin; rewrite ocd !mem_cat xin orbT.
  exists (close_cell (point e) c).
    by apply: map_f.
  rewrite /inside_closed_cell.
  move: ins; rewrite inside_open'E andbA=>/andP[] ctn /andP[liml _] /=.
  move: ctn=>/andP [qlc qhc].
  rewrite /contains_point/close_cell /=.
  have [p1 vip1] := exists_point_valid (proj1 (andP (allval _ cin))).
  have [p2 vip2] := exists_point_valid (proj2 (andP (allval _ cin))).
  have [onl x1] := intersection_on_edge vip1.
  have [onh x2] := intersection_on_edge vip2.
  by rewrite inside_closed'E vip1 vip2 qlc qhc; case: ifP=> [p1e | p1ne];
    case: ifP=> [p2e | p2ne]; rewrite liml /right_limit /= -?x2 -?x1.
move: qleft; rewrite -lexePtNgt lexePt_eqVlt.
have svalcc :
   forall c : cell,
     c \in cc -> valid_edge (low c) (point e) && valid_edge (high c) (point e).
   by move=> x /subcc xin; apply: (allP sval).
move=> /orP[/eqP qe' | qlte ].
  rewrite qe'.
  apply/orP; right; apply/hasP.
  set opc := head dummy_cell cc.
  have opcin : opc \in cc by rewrite /opc ccq /= !inE eqxx.
  have opcin' : opc \in open by rewrite subcc.
  have adjcc : adjacent_cells cc.
    by move: adj; rewrite ocd => /adjacent_catW[] _ /adjacent_catW[].
  have [leftb | nleftb] :=
    boolP(p_x (last dummy_pt (left_pts opc)) < p_x (point e)); last first.
    have notinopen : {in open, forall c, ~~ inside_open' (point e) c}.
      move=> c; rewrite ocd !mem_cat orbCA => /orP[]; last first.
        rewrite inside_open'E; move=> cold; apply/negP=> inec; move: cold.
        move=> /(decomposition_not_contain rfo sval adj cbtom inbox_e oe)[].
        by rewrite /contains_point; move: inec=> /andP[] -> /andP[] /underWC ->.
      rewrite ccq inE=> /orP[/eqP -> | ].
        rewrite inside_open'E; apply/negP=> inlec; case/negP: nleftb.
        move: inlec=> /andP[] _ /andP[] _ /andP[] + _.
        by rewrite /left_limit /opc ccq.
      move/mem_seq_split=> [s1 [s2 cc'q]].
      have hls1q : high (last lec s1) = low c.
        move: adjcc; rewrite /adjacent_cells ccq cc'q /= cat_path=> /andP[] _.
        by rewrite /= => /andP[] /eqP.
      have llecin : last lec s1 \in cc.
        rewrite ccq cc'q -[_ :: _]/((lec :: s1)++ (c :: s2)).
        by rewrite mem_cat mem_last.
      have : point e <<= low c.
        have := open_cells_decomposition_contains oe llecin=> /andP[] _.
        by rewrite hls1q.
      by rewrite inside_open'E => ->; rewrite !andbF.
    move: (cov (point e) inbox_e (lexePt_refl _)) => /orP[] /hasP [x xin Px].
      by have := notinopen x xin; rewrite Px.
    by exists x => //; rewrite -closed'eq mem_cat xin.
  have : inside_open' (point e) opc.
    have elt : all (lexePt (point e)) [seq point e0 | e0 <- e :: evs].
      rewrite /=; rewrite lexePt_eqVlt eqxx /=.
      move: sortevs; rewrite /=; rewrite path_sortedE; last exact: lexPt_trans.
      by move=> /andP[+ _]; apply: sub_all; move=> y; apply: lexPtW.
    have : contains_point' (point e) opc.
      have := open_cells_decomposition_contains oe opcin.
      rewrite /contains_point'=> /andP[] _ ->.
      rewrite /opc ccq /= leq.
      by have [-> _] := l_h_above_under_strict cbtom adj inbox_e sval rfo oe.
    by apply: (contains_to_inside_open' sval clae inbox_e leftb).
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

End proof_environment.

Notation open_cell_side_limit_ok :=
  (@open_cell_side_limit_ok R).

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
  have:= opening_cells_aux_subset cin; rewrite inE => /andP[] /orP[/eqP -> | +] _. 
    by rewrite map_f ?orbT //.
  by rewrite (perm_mem (permEl (perm_sort _ _))) => ->; rewrite ?orbT.
move/mapP=> [c cin ->].
have:= opening_cells_aux_subset cin.
rewrite !inE => /andP[] _ /orP[/eqP -> | +].
  by rewrite map_f ?orbT //.
by rewrite (perm_mem (permEl (perm_sort _ _))) => ->; rewrite ?orbT.
Qed.

Lemma inside_box_left_ptsP bottom top p :
  inside_box bottom top p -> left_limit (start_open_cell bottom top)  < p_x p.
Proof.
move=> /andP[] _ /andP[] valb valt.
move: valb valt=> /andP[] pgelb plerb /andP[] pgelt plert.
rewrite /start_open_cell/left_limit/leftmost_points; case: ifP=> cmpl.
  have /exists_point_valid [p1 p1P] : valid_edge bottom (left_pt top).
    rewrite /valid_edge (ltW cmpl) /=.
    by apply: ltW; apply: (lt_trans pgelt).
  rewrite p1P /=.
  by move: (intersection_on_edge p1P) => [] _ <-.
move/negbT: cmpl; rewrite -leNgt=>cmpl.
have /exists_point_valid [p1 p1P] : valid_edge top (left_pt bottom).
  rewrite /valid_edge cmpl /=.
  by apply/ltW; apply: (lt_trans pgelb).
by rewrite p1P /=.
Qed.

Lemma start_cover (bottom top : edge) (s : seq edge) closed open :
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, no_crossing R} ->
  all (inside_box bottom top) [seq left_pt x | x <- s] ->
  all (inside_box bottom top) [seq right_pt x | x <- s] ->
  start (edges_to_events s) bottom top = (closed, open) ->
  forall p, inside_box bottom top p ->
  has (inside_closed' p) closed || has (inside_open' p) open.
Proof.
move=> boxwf boxwf2 nocs leftin rightin; rewrite /start.
set evs := edges_to_events s.
have/perm_mem := edges_to_events_no_loss s.
  rewrite -/evs/events_to_edges/= => stoevs.
set op0 := [:: Bcell (leftmost_points bottom top) [::] bottom top].
set cl0 := (X in scan _ _ X).
have : sorted (@lexPt R) [seq point x | x <- evs].
  by apply: sorted_edges_to_events.
have : cells_bottom_top bottom top op0.
  by rewrite /op0/cells_bottom_top/cells_low_e_top/= !eqxx.
have : adjacent_cells op0 by [].
have : s_right_form op0 by rewrite /= boxwf.
have : close_alive_edges bottom top op0 evs.
  by rewrite /=/end_edge !inE !eqxx !orbT.
have : {in cell_edges op0 ++ flatten [seq outgoing i | i <- evs] &,
         no_crossing R}.
  rewrite /=; move: nocs; apply sub_in2.
  move=> x; rewrite !inE => /orP[ -> // | /orP[-> // | ]]; rewrite ?orbT //.
  by rewrite -stoevs => ->; rewrite ?orbT.
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
  rewrite /op0 inE /lexPt /bottom_left_corner=> /eqP -> /=.
  by apply/orP; left; apply/inside_box_left_ptsP/(allP evsin0).
have sval0 :
  evs != nil -> seq_valid op0 (head dummy_pt [seq point ev | ev <- evs]).
  case evseq : evs => [// | ev evs'] _ /=; rewrite andbT.
  move: evsin0; rewrite evseq /= => /andP[] /andP[] _ /andP[] ebot etop _.
  have betW : forall a b c : R, a < b < c -> a <= b <= c.
    by move=> a b c /andP[] h1 h2; rewrite !ltW.
  by rewrite /valid_edge !betW.
have cov0 : forall p, all (lexePt p) [seq point ev | ev <- evs] ->
         cover_left_of bottom top p op0 cl0.
  move=> p limrp q inbox_q qp; apply/orP; left; apply/hasP.
  exists (Bcell (leftmost_points bottom top) nil bottom top).
    by rewrite /op0 inE eqxx.
  rewrite inside_open'E.
  apply/andP; split;[ | apply/andP; split].
  - by apply: underW; move: inbox_q=> /andP[] /andP[].
  - by move: inbox_q=> /andP[] /andP[].
  - rewrite /open_limit /=.
    case: (ltrP  (p_x (right_pt bottom)) (p_x (right_pt top))) => _.
    rewrite inside_box_left_ptsP //.
    by move: inbox_q => /andP[] _ /andP[] /andP[] _ /ltW ->.
  rewrite inside_box_left_ptsP //.
  by move: inbox_q => /andP[] _ /andP[] _ /andP[] _ /ltW ->.
have leftlim0 : {in op0, forall c p, inside_box bottom top p ->
         left_limit c = p_x p ->
         contains_point' p c -> has (inside_closed' p) cl0}.
  move=> c + p; rewrite inE -[Bcell _ _ _ _]/(start_open_cell bottom top).
  move=> /eqP -> {c}.
  move/inside_box_left_ptsP/[swap].
  by rewrite (leftmost_points_max boxwf2)=> ->; rewrite lt_irreflexive.
move: cov0 evsin0 sval0 btm_left0 leftlim0; move=> {stoevs}.
elim: evs op0 cl0 => [ | ev evs' Ih]
   op cl main evsin sval btm_left llim clev oute noc clae rfo adj cbtom sortev.
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
  move: sortev; rewrite /sorted /=.
  rewrite  (path_sortedE (@lexPt_trans R)) // => /andP[+ _].
  by apply: sub_all; exact: lexPtW.
have cov' : forall p : pt,
    all (lexePt p) [seq point ev0 | ev0 <- evs'] ->
    cover_left_of bottom top p op' cl'.
  have := step_keeps_cover sortev cbtom adj inbox_e sval' oute' rfo clae clev
           noc btm_left' llim stepeq cov.
  move=> it p; apply: it.
have evle : forall ev', ev' \in evs' -> lexPt (point ev) (point ev').
  move=> ev' ev'in.
  move: sortev=> /=; rewrite (path_sortedE (@lexPt_trans R))=> /andP[]/allP.
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
      by move=>/andP[]/allP/(_ (point e') (map_f (@point _) e'q))/lexPtW.
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
have nocr : {in cell_edges op' ++ flatten [seq outgoing i | i <- evs'] &,
     no_crossing R}.
  move: noc; apply: sub_in2=> x.
  rewrite mem_cat=> /orP[].
    move/(step_sub_open_edges cbtom adj inbox_e stepeq)=> it.
    by rewrite /= /cell_edges catA -(catA _ _ (outgoing ev)) mem_cat it.
  by move=> xinf; rewrite /= !mem_cat xinf !orbT.
have claer : close_alive_edges bottom top op' evs'.
  by have := step_keeps_closeness inbox_e oute' rfo cbtom adj sval' clev
      clae stepeq.
have rfor : s_right_form op'.
  have noc1: {in  cell_edges op ++ outgoing ev &, no_crossing R}.
    move: noc; apply sub_in2=> x.
    rewrite mem_cat=> /orP[it| xino].
      by rewrite /= /cell_edges catA 2!mem_cat it.
    by rewrite /= !mem_cat xino !orbT.
  by apply: (step_keeps_right_form cbtom adj inbox_e sval' noc1 _ _ stepeq).
have adjr : adjacent_cells op'.
  by have := step_keeps_adjacent inbox_e oute' sval' cbtom stepeq adj.
have cbtomr : cells_bottom_top bottom top op'.
  by apply: (step_keeps_bottom_top inbox_e sval' adj cbtom oute' stepeq).
have sortev' : sorted (@lexPt R) [seq point x | x <- evs'].
  by move: sortev; rewrite /= => /path_sorted.
have llim' : {in op', forall c p, inside_box bottom top p ->
                  left_limit c = p_x p -> 
                  contains_point' p c -> has (inside_closed' p) cl'}.
  by apply: (step_keeps_cover_left_border cbtom adj inbox_e sval' oute' rfo clae
       clev noc btm_left' stepeq llim).
by have := Ih _ _ cov' evsinr svalr btm_leftr llim' clevr outer nocr claer
  rfor adjr cbtomr sortev' scaneq.
Qed.

Lemma cell_edges_start bottom top :
  cell_edges [::(start_open_cell bottom top)] = [:: bottom; top].
Proof. by []. Qed.

Lemma start_disjoint bottom top s closed open evs :
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq left_pt x | x <- s] ->
  all (inside_box bottom top) [seq right_pt x | x <- s] ->
  all (inside_box bottom top) [seq point e | e <- evs] ->
  sorted (@lexPtEv _) evs ->
  {subset flatten [seq outgoing e | e <- evs] <= s} ->
  {in evs, forall ev, out_left_event ev} ->
  close_edges_from_events bottom top evs ->
  start evs bottom top = (closed, open) ->
  {in closed &, disjoint_closed_cells R} /\
  {in open & closed, disjoint_open_closed_cells R}.
Proof.
move=> boxwf startok nocs' leftin rightin evin lexev evsub out_evs cle.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
rewrite /start.
set op0 := [:: start_open_cell bottom top].
set cl0 := (X in scan _ _ X).
have op0sok : all open_cell_side_limit_ok op0.
  by rewrite /= startok.
have cbtom0 : cells_bottom_top bottom top op0.
  by rewrite /op0/cells_bottom_top/cells_low_e_top/= !eqxx.
have adj0: adjacent_cells op0 by [].
have rf0: s_right_form op0 by rewrite /= boxwf.
have claev0 : close_alive_edges bottom top op0 evs.
  by rewrite /=/end_edge !inE !eqxx !orbT.
have noc0 : {in cell_edges op0 ++ flatten [seq outgoing i | i <- evs] &,
         no_crossing R}.
  rewrite /=; move: nocs; apply sub_in2.
  move=> x; rewrite !inE => /orP[ -> // | /orP[-> // | ]]; rewrite ?orbT //.
  by move=> /evsub ->; rewrite !orbT.
have evsin0 : all (inside_box bottom top) [seq point ev | ev <- evs].
  exact: evin.
have sval0 :
  evs != nil -> seq_valid op0 (head dummy_pt [seq point ev | ev <- evs]).
  case evseq : evs => [// | ev evs'] _ /=; rewrite andbT.
  move: evsin0; rewrite evseq /= => /andP[] /andP[] _ /andP[] ebot etop _.
  have betW : forall a b c : R, a < b < c -> a <= b <= c.
    by move=> a b c /andP[] h1 h2; rewrite !ltW.
  by rewrite /valid_edge !betW.
have dis0 : {in cl0 &, disjoint_closed_cells R} /\
            {in op0 & cl0, disjoint_open_closed_cells R} by [].
have edges_sub : {subset all_edges op0 evs <= [:: bottom, top & s]}.
  move=> e.
  rewrite mem_cat !inE => /orP[] /=; last first.
    by move=> /evsub => ->; rewrite !orbT.
  by move=>  /orP[] /eqP ->; rewrite eqxx ?orbT.
have op_dis0 : {in op0 &, disjoint_open_cells R}.
  by move=> g1 g2; rewrite !inE => /eqP <-; left; apply/esym/eqP.
have esp0 : edge_side evs op0.
  rewrite /edge_side /edge_side_prop.
  case evseq : evs => [ // | ev evs' /=].
  have pin : inside_box bottom top (point ev).
    by apply: (allP evsin0); rewrite evseq /= inE eqxx.
  rewrite (inside_box_valid_bottom_top pin); last by rewrite !inE eqxx orbT.
  move: pin => /andP[] _ /andP[] _ /andP[] -> ->.
  by case: ifP => //; case: ifP.
have right_lims0 :
    {in evs & cl0, forall ev c, right_limit c  <= p_x (point ev)}.
  by [].
move: op0sok op_dis0 dis0 evsin0 sval0 edges_sub evin lexev
 evsub cle claev0 out_evs rf0 adj0 cbtom0 noc0 esp0 right_lims0.
elim: evs op0 cl0 => [ | ev evs' Ih] /=.
  rewrite /= => op cl opsok op_disj disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  move=> [] <- <-; exact: disj.
move=> op cl osok odis [cdis ocdis] /andP[] inbox_e inbox
  /(_ isT) sval edges_sub /andP[] evin evsin lexev sub_all clee clae
  out_evs rfo adj cbtom noc esp right_lims_evs.
case stepeq : (step ev op cl)=> [open' closed'].
have noc2: {in [seq low c | c <- op] ++ [seq high c | c <- op] ++ outgoing ev &,
        forall e1 e2, inter_at_ext e1 e2}.
  apply: (sub_in2 _ nocs') => g gin; apply: edges_sub; rewrite mem_cat.
  move: gin; rewrite catA mem_cat=> /orP[-> // | /=].
  by rewrite /events_to_edges /= [X in _ || X]mem_cat orbCA => ->.
have noc3: {in cell_edges op ++ outgoing ev &, no_crossing R}.
  by apply: (sub_in2 _ noc)=> c cin; rewrite catA mem_cat cin.
have out_e : out_left_event ev by apply: out_evs; rewrite inE eqxx.
have lexv' : all [eta lexPtEv ev] evs'.
  by apply: (order_path_min (@lexPtEv_trans _)).
have right_lims : {in cl, forall c, right_limit c <= p_x (point ev)}.
  by move=> c; apply: right_lims_evs; rewrite inE eqxx.
have allin : all (inside_box bottom top) [seq point e | e <- evs'].
  by apply/allP=> g gin; apply: (allP inbox g).
have hdin : evs' != [::] -> inside_box bottom top 
   (head dummy_pt [seq point e | e <- evs']).
  case evs'eq : evs' => [ // | ev1 evs'' /=] _.
  by apply: (allP evsin); rewrite evs'eq /= inE eqxx.
have sval1 : evs' != [::] ->
    seq_valid open' (head dummy_pt [seq point ev0 | ev0 <- evs']).
  move=> /[dup] evs'n0; case evs'eq : evs' => [ // | ev1 evs''] _.
  have := (step_keeps_valid (hdin evs'n0) _ _ _ _ _ _ _ clae _ _ stepeq).
  rewrite -evs'eq; apply => //.
  * rewrite evs'eq /=.
    have := allP (order_path_min (@lexPtEv_trans _) lexev).
    by move=> /(_ ev1); rewrite evs'eq inE eqxx => /(_ isT).
  * move=> e2; rewrite evs'eq inE=> /orP[/eqP -> | ].
    ** by rewrite lexePt_refl.
    move=> e2in; apply: lexPtW.
    move: lexev=> /path_sorted; rewrite evs'eq.
    by move=>/(order_path_min (@lexPtEv_trans _))/allP /(_ _ e2in).
have clae' : close_alive_edges bottom top open' evs'.
  exact: (step_keeps_closeness inbox_e out_e rfo cbtom adj sval _ _ stepeq).
apply: Ih => //.
- by apply: (step_keeps_open_cell_side_limit cbtom adj inbox_e sval
             out_e rfo noc3  stepeq osok).
- by apply: (step_keeps_disjoint_open cbtom adj inbox_e sval rfo noc2
        odis out_e osok esp clae lexv' stepeq).
- exact: (step_keeps_disjoint cbtom adj _ _ _ _ _ _ _ _ _ _ _ clae _ stepeq).
- move=> g; rewrite mem_cat=> /orP[]; last first.
    move=> gin; apply: edges_sub; rewrite mem_cat orbC /events_to_edges /=.
    by rewrite mem_cat gin !orbT.
  move/(step_keeps_subset cbtom adj inbox_e stepeq)=> gin.
  apply: edges_sub; rewrite mem_cat /events_to_edges /= [X in _ || X]mem_cat.
  by rewrite orbA -mem_cat gin.
- exact: (path_sorted lexev).
- by move=> g gin; apply: sub_all; rewrite mem_cat gin orbT.
- by move: clee=> /andP[].
- by move=> e ein; apply: out_evs; rewrite inE ein orbT.
- exact: (step_keeps_right_form cbtom adj inbox_e sval _ _ _ stepeq).
- exact: (step_keeps_adjacent inbox_e out_e sval cbtom stepeq).
- exact: (step_keeps_bottom_top inbox_e sval adj cbtom out_e stepeq).
- move=> g1 g2; rewrite mem_cat=> g1in; rewrite mem_cat=> g2in; apply: noc;
  rewrite mem_cat [X in _ || X]mem_cat.
    move: g1in=> /orP[ | ->]; last by rewrite !orbT.
    move/(step_keeps_subset cbtom adj inbox_e stepeq)=> gin.
    by rewrite orbA -mem_cat gin.
  move: g2in=> /orP[ | ->]; last by rewrite !orbT.
  move/(step_keeps_subset cbtom adj inbox_e stepeq)=> gin.
  by rewrite orbA -mem_cat gin.
- apply:(step_keeps_edge_side stepeq _ out_e _ cbtom)=> //.
  * by rewrite /= evin.
have right_lims' := step_keeps_closed_to_the_left cbtom adj sval inbox_e rfo
         stepeq right_lims.
move=> ev1 c ev1in cin.
apply: (le_trans (right_lims' c cin)).
have : lexPtEv ev ev1 by exact: (allP lexv' _ ev1in).
by move=>/orP[ | /andP[] + _]; rewrite ?le_eqVlt=> ->; rewrite ?orbT.
Qed.

Lemma start_edge_covering bottom top s (evs : seq event) open closed :
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in [:: bottom, top & s] &, forall e1 e2, inter_at_ext e1 e2} ->
  {in [:: bottom, top & s] & [seq point e | e <- evs],
     forall g e, non_inner g e} ->
  all (inside_box bottom top) [seq point e | e <- evs] ->
  sorted (@lexPtEv _) evs ->
  {subset flatten [seq outgoing e | e <- evs] <= s} ->
  uniq (flatten [seq outgoing e | e <- evs]) ->
  {in evs, forall ev : event, out_left_event ev} ->
  close_edges_from_events bottom top evs ->
  start evs bottom top = (closed, open) ->
  {in evs, forall ev, forall g, g \in outgoing ev ->
     edge_covered g open closed}.
Proof.
move=> boxwf startok nocs' nonin evin lexev evsub uni out_evs cle.
rewrite /start.
set op0 := [:: start_open_cell bottom top].
set cl0 := (X in scan _ _ X).
have op0sok : all open_cell_side_limit_ok op0.
  by rewrite /= startok.
have cbtom0 : cells_bottom_top bottom top op0.
  by rewrite /op0/cells_bottom_top/cells_low_e_top/= !eqxx.
have adj0: adjacent_cells op0 by [].
have rf0: s_right_form op0 by rewrite /= boxwf.
have claev0 : close_alive_edges bottom top op0 evs.
  by rewrite /=/end_edge !inE !eqxx !orbT.
have evsin0 : all (inside_box bottom top) [seq point ev | ev <- evs].
  exact: evin.
have sval0 :
  evs != nil -> seq_valid op0 (head dummy_pt [seq point ev | ev <- evs]).
  case evseq : evs => [// | ev evs'] _ /=; rewrite andbT.
  move: evsin0; rewrite evseq /= => /andP[] /andP[] _ /andP[] ebot etop _.
  have betW : forall a b c : R, a < b < c -> a <= b <= c.
    by move=> a b c /andP[] h1 h2; rewrite !ltW.
  by rewrite /valid_edge !betW.
have op0sub : {subset cell_edges op0 <= [:: bottom, top & s]}.
  by rewrite cell_edges_start=> g; rewrite !inE orbA=> ->.
move=> scaneq.
suff main: forall g, 
        edge_covered g op0 cl0 \/ g \in flatten [seq outgoing e | e <- evs] ->
        edge_covered g open closed.
  move=> e ein g gin; apply: main; right.
  by apply/flattenP; exists (outgoing e);[apply/map_f | ].
have btm_left0 : {in [seq point e | e <- evs], 
         forall e,  bottom_left_cells_lex op0 e}.
  move=> ev /[dup] /(allP evsin0) /andP[_ /andP[valb valt]] evin' c.
  rewrite /op0 inE /lexPt /bottom_left_corner=> /eqP -> /=.
  by apply/orP; left; apply/inside_box_left_ptsP/(allP evsin0).
have inj0 : {in op0 &, injective (@high R)}.
  by move=> c1 c2; rewrite !inE => + => /eqP <- /eqP ->.
move: cbtom0 adj0 rf0 claev0 evsin0 sval0 op0sok evin lexev evsub out_evs
  uni cle nonin op0sub btm_left0 inj0 scaneq.
(*****)
elim: evs op0 cl0 => [ | e evs Ih] op cl cbtom adj rfo clae allin sval' allok
  evin lexev evsub out_evs uni clev nonin opsub btm_left inj.
  by move=> /= -[] <- <- g [// | //].
rewrite /=.
case stepeq : (step e op cl) => [op' cl'] scaneq.
have inbox_e : inside_box bottom top (point e).
  by apply: (allP allin); rewrite map_f // inE eqxx.
have {sval'}sval : seq_valid op (point e) by apply: sval'.
have oute : out_left_event e by apply: out_evs; rewrite inE eqxx.
have cbtom' : cells_bottom_top bottom top op'.
  exact: (step_keeps_bottom_top inbox_e sval adj cbtom oute stepeq).
have adj' : adjacent_cells op'.
  exact: (step_keeps_adjacent inbox_e oute sval cbtom stepeq adj).
have noc : {in cell_edges op ++ outgoing e &, no_crossing R}.
  apply: inter_at_ext_no_crossing.
  apply: (sub_in2 _ nocs').
  move=> g; rewrite mem_cat=> /orP[ | ino]; first exact: opsub.
  by rewrite !inE evsub ?orbT //= mem_cat ino.
have rfo' : s_right_form op'.
  exact: (step_keeps_right_form cbtom adj inbox_e sval noc oute rfo stepeq).
have clae' : close_alive_edges bottom top op' evs.
  by apply: (step_keeps_closeness inbox_e oute rfo _ adj sval clev clae stepeq).
have allin' : all (inside_box bottom top) [seq point ev | ev <- evs].
  by apply/allP=> p pin; apply: (allP allin p); rewrite inE pin orbT.
move: lexev; rewrite /= path_sortedE; last by apply: lexPtEv_trans.
move=> /andP[] /allP=> lexev lexev1.
have sval' :
 evs != [::] -> seq_valid op' (head dummy_pt [seq point ev | ev <- evs]).
  case evsq : evs => [// | ev1 evs'] _ /=.
  rewrite evsq in lexev lexev1.
  have ele1: lexPt (point e) (point ev1) by apply: lexev; rewrite inE eqxx.
  move: lexev1; rewrite /= path_sortedE; last by apply: lexPtEv_trans.
  move=> /andP[] lexev1 lexev1'.
  have lexev2 : {in evs, forall e, lexePt (point ev1) (point e)}.
    move=> e'; rewrite evsq inE=> /orP[/eqP -> |]; first by apply:lexePt_refl.
   by move=> e'in; apply/lexPtW; apply: (allP lexev1).
  have ev1in : inside_box bottom top (point ev1).
    by apply: (allP allin); rewrite evsq map_f // !inE eqxx ?orbT.
  by apply: (step_keeps_valid ev1in inbox_e ele1 oute _ _ _ _ _ clev
            lexev2 stepeq).
have opok' :all open_cell_side_limit_ok op'.
  by apply: (step_keeps_open_cell_side_limit cbtom _ _ _ _ _ noc stepeq allok).
have evin' : all (inside_box bottom top) [seq point e | e <- evs].
  by apply/allP=> x xin; apply: (allP evin); rewrite /= inE xin ?orbT.
have evsub' : {subset flatten [seq outgoing e | e <- evs] <= s}.
  by move=> g gin; apply: evsub; rewrite /= mem_cat gin orbT.
have out_evs' : {in evs, forall ev, out_left_event ev}.
  by move=> e' e'in; apply: out_evs; rewrite /= inE e'in orbT.
have uni' : uniq (flatten [seq outgoing e | e <- evs]).
  by move: uni; rewrite /= cat_uniq=> /andP[] _ /andP[] _.
have clev' : close_edges_from_events bottom top evs.
  by move: clev=> /= /andP[].
have nonin' : {in [:: bottom, top & s] & [seq point e | e <- evs],
        forall g p, non_inner g p}.
   by move=> g p gin pin; apply nonin; rewrite //= inE pin orbT.
have opsub': {subset cell_edges op' <= [:: bottom, top & s]}.
  move=> g /(step_keeps_subset cbtom adj inbox_e stepeq); rewrite mem_cat.
  move=> /orP[/opsub //| gout ].
  move: evsub=> /= /(_ g); rewrite mem_cat gout !inE=> -> //.
  by rewrite !orbT.  
have noc1 : {in all_edges op (e :: evs) &, no_crossing R}.
  apply: inter_at_ext_no_crossing.
  apply: (sub_in2 _ nocs').
  move=> g; rewrite mem_cat=> /orP[].
    by apply: opsub.
  by move/evsub; rewrite !inE => ->; rewrite ?orbT.
have btm_left_e : bottom_left_cells_lex op (point e).
  by apply: btm_left; rewrite map_f // inE eqxx.
have btm_left' : {in [seq point e | e <- evs], forall p, bottom_left_cells_lex op' p}.
  have btm_left2 :=
    step_keeps_left_pts_inf inbox_e oute rfo sval adj cbtom clae clev
           noc1 btm_left_e stepeq.
  by move=> p /mapP [ev' ev'in ->]; apply/btm_left2/lexev.
have ninnere : open_non_inner_event op e.
  rewrite /open_non_inner_event.
  move=> c cin; apply: nonin.
    by apply: opsub; rewrite mem_cat map_f ?orbT.
  by rewrite inE eqxx.
have inj' : {in op'&, injective (@high R)}.
  have unie : uniq (outgoing e).
    by move: uni; rewrite /= cat_uniq => /andP[].
  have hlex := bottom_left_lex_to_high cbtom adj rfo allok inbox_e btm_left_e.
  by apply : (step_keeps_injective_high cbtom _ _ _ _ _ unie hlex stepeq inj).
have {}Ih:= (Ih op' cl' cbtom' adj' rfo' clae' allin' sval' opok' evin' lexev1
         evsub' out_evs' uni' clev' nonin' opsub' btm_left' inj' scaneq ).
have step_edge_covering:=
   (step_keeps_edge_covering allok btm_left_e ninnere inj cbtom adj inbox_e
       sval rfo oute _ stepeq).
move=> g [gc | gev].
  by apply: Ih; left; apply: step_edge_covering; left.
move: gev; rewrite mem_cat=> /orP[gout | gev].
  by apply: Ih; left; apply: step_edge_covering; right.
by apply: Ih; right.
Qed.

End working_environment.
