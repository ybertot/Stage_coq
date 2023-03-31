From mathcomp Require all_ssreflect.
Require Import ZArith QArith List String.

Notation seq := list.
Record pt := Bpt {p_x : Q; p_y : Q}.
Record edge :=
 Bedge { left_pt : pt; right_pt : pt}.

Record event :=
  Bevent {point : pt; outgoing : seq edge}.

Record cell := Bcell  {left_pts : list pt; right_pts : list pt;
                        low : edge; high : edge}.

Definition dummy_pt := ({| p_x := 0%Q; p_y := 0%Q|}).
Notation DUMMY_PT := 
  ({| p_x := (0 # _); p_y := (0 # _)|}).

Definition dummy_edge := 
  {| left_pt := dummy_pt; right_pt := dummy_pt|}.

Notation DUMMY_EDGE :=
  ({| left_pt := DUMMY_PT; right_pt := DUMMY_PT |}).

Definition dummy_cell := 
  {| left_pts := nil; right_pts := nil; low := dummy_edge; high := dummy_edge|}.

Notation DUMMY_CELL :=
  ({| left_pts := nil; right_pts := nil; 
    low := DUMMY_EDGE; high := DUMMY_EDGE|}).

Definition dummy_event :=
  {| point := dummy_pt; outgoing := nil|}.

Definition pt_eqb (a b : pt) : bool :=
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
     (Qeq_bool a_x b_x)%Q && (Qeq_bool a_y b_y).

Definition Qlt_bool (q1 q2 : Q) : bool :=
  negb (Qle_bool q2 q1).

Fixpoint add_event (p : pt) (e : edge) (inc : bool) (evs : seq event) :
  seq event :=
  match evs with
  | nil => if inc then (Bevent p nil :: nil)
           else (Bevent p (e :: nil) :: nil)
  | ev1 :: evs' =>
    let p1 := point ev1 in
    if pt_eqb p p1 then
      if inc then Bevent p1 (outgoing ev1) :: evs'
      else Bevent p1 (e :: outgoing ev1) :: evs' else
    if Qlt_bool (p_x p) (p_x p1) then
      if inc then
        Bevent p nil :: evs else
        Bevent p (e :: nil) :: evs
    else if Qeq_bool (p_x p) (p_x p1) && Qlt_bool (p_y p) (p_y p1) then
       if inc then
         Bevent p nil :: evs else
         Bevent p (e :: nil) :: evs else
    ev1 :: add_event p e inc evs'
  end.

Fixpoint edges_to_events (s : seq edge) : seq event :=
  match s with
  | nil => nil
  | e :: s' =>
    add_event (left_pt e) e false
      (add_event (right_pt e) e true (edges_to_events s'))
  end.

(* this function removes consecutives duplicates, meaning the seq needs
 to be sorted first if we want to remove all duplicates *)
Fixpoint no_dup_seq [A : Type] (eqb : A -> A -> bool) (s : seq A) : (seq A) :=
  match s with
  | nil => nil
  | a::q =>
    match q with
    | nil => s
    | b::r =>
      if eqb a b then no_dup_seq eqb q else a::(no_dup_seq eqb q)
    end
  end.

Definition valid_edge e p := (Qle_bool (p_x (left_pt e)) (p_x p)) &&
(Qle_bool (p_x p) (p_x (right_pt e))).

Definition vertical_intersection_point (p : pt) (e : edge) : option pt :=
  if valid_edge e p then Some(Bpt (p_x p) (((p_x p) - p_x (left_pt e))
   * (((p_y (right_pt e)) - p_y (left_pt e)) /
    ((p_x (right_pt e)) - p_x (left_pt e))) + p_y (left_pt e)))
    else None.


Definition close_cell (p : pt) (c : cell) :=
  match vertical_intersection_point p (low c),
        vertical_intersection_point p (high c) with
  | None, _ | _, None => c
  | Some p1, Some p2 => 
    Bcell (left_pts c) (no_dup_seq pt_eqb (p1 :: p :: p2 :: nil)) (low c) (high c)
  end.

Definition closing_cells (p : pt) (contact_cells: seq cell) : seq cell :=
  List.map (fun c => close_cell p c) contact_cells.

Fixpoint opening_cells_aux (p : pt) (out : seq edge) (low_e high_e : edge) 
  : seq cell * cell :=
      match out with
    | nil => let op0 := vertical_intersection_point p low_e in
              let op1 := vertical_intersection_point p high_e in
                      match (op0,op1) with
                          |(None,_) |(_,None)=> (nil, dummy_cell)
                          |(Some(p0),Some(p1)) =>
                              (nil , 
                              Bcell  (no_dup_seq pt_eqb (p1 :: p :: p0 :: nil)) nil low_e high_e)                      end
    | c::q => let op0 := vertical_intersection_point p low_e in
              let (s, nc) := opening_cells_aux p q c high_e in
                    match op0 with
                       | None => (nil, dummy_cell)
                       | Some(p0) =>
                        (Bcell  (no_dup_seq pt_eqb (p :: p0 :: nil)) nil low_e c :: s,
                         nc)
                    end
end.

Definition pue_formula (p : pt) (a : pt) (b : pt) : Q :=
  let: Bpt p_x p_y := p in
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
  ((b_x * p_y - p_x * b_y - (a_x * p_y - p_x * a_y) + a_x * b_y - b_x * a_y))%Q.

Definition point_under_edge (p : pt) (e : edge) : bool :=
  Qle_bool (pue_formula p (left_pt e) (right_pt e)) 0.

Definition point_strictly_under_edge (p : pt) (e : edge) : bool :=
  Qlt_bool (pue_formula p (left_pt e) (right_pt e)) 0.

Definition edge_below (e1 : edge) (e2 : edge) : bool :=
(point_under_edge (left_pt e1) e2 && 
 point_under_edge (right_pt e1) e2)
|| (negb (point_strictly_under_edge (left_pt e2) e1) && 
   negb (point_strictly_under_edge (right_pt e2) e1)).


Definition opening_cells (p : pt) (out : seq edge) (l h : edge) : seq cell :=
   let (s, c) := opening_cells_aux p (path.sort edge_below out) l h in
   seq.rcons s c.

Definition contains_point (p : pt) (c : cell)  : bool :=
   negb (point_strictly_under_edge p (low c)) && point_under_edge p (high c).

Fixpoint open_cells_decomposition_contact open_cells pt :
   option (seq cell * seq cell * cell) :=
match open_cells with
| c :: q => 
  if contains_point pt c then
    match open_cells_decomposition_contact q pt with
    | Some(cc, lc, c') => Some(c :: cc, lc, c')
    | None => Some(nil, q, c)
    end
  else
    None
| nil => None
end.

Fixpoint open_cells_decomposition_rec open_cells pt : 
  seq cell * seq cell * cell * seq cell :=
match open_cells with
| c :: q =>
  if contains_point pt c then
     match open_cells_decomposition_contact q pt with
     | Some(cc, lc, c') => (nil, c :: cc, c', lc)
     | None => (nil, nil, c, q)
     end
  else
    let '(fc, cc, c', lc) := open_cells_decomposition_rec q pt in
    (c :: fc, cc, c', lc)
| nil => (nil, nil, dummy_cell, nil)
end.

Definition open_cells_decomposition (open_cells : seq cell) (p : pt) :
   seq cell * seq cell * cell * seq cell * edge * edge :=
let '(fc, cc, c', lc) := open_cells_decomposition_rec open_cells p in
(fc, cc, c', lc, low (seq.head c' cc), high c').

Record scan_state :=
  Bscan {sc_open1 : seq cell;
         lst_open : cell;
         sc_open2 : seq cell;
         sc_closed : seq cell;
         lst_closed : cell;
         lst_high : edge;
         lst_x : Q}.

Definition update_closed_cell (c : cell) (p : pt) : cell :=
  let ptseq := right_pts c in
  let newptseq :=
    (seq.belast  (seq.head dummy_pt ptseq) (seq.behead ptseq)) ++
    (p :: seq.last dummy_pt ptseq :: nil) in
  Bcell (left_pts c) newptseq (low c) (high c).

Definition update_open_cell (c : cell) (e : event) : seq cell * cell :=
  match outgoing e with
  | nil =>
     let ptseq := left_pts c in
     let newptseq :=
       (seq.head dummy_pt ptseq :: point e :: seq.behead ptseq) in
     (nil, Bcell newptseq (right_pts c) (low c) (high c))
  | _ =>
    opening_cells_aux (point e) (path.sort edge_below (outgoing e))
        (low c) (high c)
  end.

Definition pvert_y (p : pt) (e : edge) :=
  match vertical_intersection_point p e with
    Some p' => p_y p'
  | None => 0
  end.

Definition update_open_cell_top (c : cell) (new_high : edge) (e : event) :=
  match outgoing e with
  | nil =>
    let newptseq :=
      (Bpt (p_x (point e)) (pvert_y (point e) new_high) ::
          left_pts c) in
      (nil, Bcell newptseq (right_pts c) (low c) new_high)
  | _ => 
    opening_cells_aux (point e) (path.sort edge_below (outgoing e))
        (low c) new_high
  end.

Definition step (e : event) (st : scan_state) : scan_state :=
   let p := point e in
   let '(Bscan op1 lsto op2 cls cl lhigh lx) := st in
   if negb (Qeq_bool (p_x p) lx) then
     let '(first_cells, contact_cells, last_contact, last_cells, 
           lower_edge, higher_edge) :=
       open_cells_decomposition (op1 ++ lsto :: op2) p in
     let closed := closing_cells p contact_cells in
     let last_closed := close_cell p last_contact in
     let closed_cells := cls ++ cl :: closed in
     let (new_open_cells, newlastopen) :=
       opening_cells_aux p (path.sort edge_below (outgoing e))
            lower_edge higher_edge in
     Bscan (first_cells ++ new_open_cells)
           newlastopen last_cells closed_cells 
           last_closed  higher_edge (p_x (point e))
   else if negb (point_under_edge p lhigh) then
     let '(fc', contact_cells, last_contact, last_cells,
           low_edge, higher_edge) :=
       open_cells_decomposition op2 p in
     let first_cells := op1 ++ lsto :: fc' in
(* TODO code duplication (6 lines above) *)
     let closed := closing_cells p contact_cells in
     let last_closed := close_cell p last_contact in
     let closed_cells := cls++closed in
     let (new_open_cells, newlastopen) :=
       opening_cells_aux p (path.sort edge_below (outgoing e))
            low_edge higher_edge in
     Bscan (first_cells ++ new_open_cells)
           newlastopen last_cells closed_cells last_closed
            higher_edge (p_x (point e))
   else if point_strictly_under_edge p lhigh then 
     let new_closed := update_closed_cell cl (point e) in
     let (new_opens, new_lopen) := update_open_cell lsto e in
     Bscan (op1 ++ new_opens) new_lopen op2 cls new_closed lhigh lx
   else (* here p === lhigh *)
     let '(fc', contact_cells, last_contact, last_cells, lower_edge,
                higher_edge) :=
       open_cells_decomposition (lsto :: op2) p in
     let closed := closing_cells p contact_cells in
     let last_closed := close_cell p last_contact in
     let (new_opens, new_lopen) := update_open_cell_top lsto higher_edge e in
     Bscan (op1 ++ fc' ++ new_opens) new_lopen last_cells
          (cls ++ closed) last_closed higher_edge lx.

Definition leftmost_points (bottom top : edge) :=
  if Qlt_bool (p_x (left_pt bottom)) (p_x (left_pt top)) then
    match vertical_intersection_point (left_pt top) bottom with
    | Some pt => left_pt top :: pt :: nil
    | None => nil
    end
  else
    match vertical_intersection_point (left_pt bottom) top with
    | Some pt => pt :: left_pt bottom :: nil
    | _ => nil
    end.

Definition rightmost_points (bottom top : edge) :=
  if Qlt_bool (p_x (right_pt bottom)) (p_x (right_pt top)) then
    match vertical_intersection_point (right_pt bottom) top with
    | Some pt => right_pt bottom :: pt :: nil
    | _ => nil
    end
  else
    match vertical_intersection_point (left_pt top) bottom with
    | Some pt => pt :: right_pt top :: nil
    | _ => nil
    end.

Definition complete_last_open (bottom top : edge) (c : cell) :=
  match c with
  | Bcell lpts rpts le he =>
      Bcell lpts (rightmost_points bottom top) le he
  end.

Definition start_open_cell (bottom top : edge) :=
  Bcell (leftmost_points bottom top) nil bottom top.

Definition start (first_event : event) (bottom : edge) (top : edge) :
  scan_state :=
  let (newcells, lastopen) :=
  opening_cells_aux (point first_event)
      (path.sort edge_below (outgoing first_event)) bottom top in
      (Bscan newcells lastopen nil nil
         (close_cell (point first_event) (start_open_cell bottom top))
         top (p_x (point first_event))).

Fixpoint iter_list [A B : Type] (f : A -> B -> B) (s : seq A) (init : B) :=
  match s with
  | nil => init
  | a :: tl => iter_list f tl (f a init)
  end.

Definition scan (events : seq event) (bottom top : edge) : seq cell :=
  match events with
  | nil => (complete_last_open bottom top (start_open_cell bottom top) :: nil)
  | ev0 :: events =>
    let start_scan := start ev0 bottom top in
    let final_scan := iter_list step events start_scan in
      lst_closed final_scan :: map (complete_last_open bottom top)
      (lst_open final_scan :: sc_open1 final_scan ++ sc_open2 final_scan) ++
      sc_closed final_scan
  end.

Definition edges_to_cells bottom top edges :=
  scan (edges_to_events edges) bottom top.

Record vert_edge :=
 { ve_x : Q; ve_top : Q; ve_bot : Q}.

Fixpoint seq_to_intervals_aux [A : Type] (a : A) (s : seq A) :=
match s with
| nil => nil
| b :: tl => (a, b) :: seq_to_intervals_aux b tl
end.

Definition seq_to_intervals [A : Type] (s : seq A) :=
match s with
  nil => nil
| a :: tl => seq_to_intervals_aux a tl
end.

Definition cell_safe_exits_left (c : cell) : seq vert_edge :=
  let lx := p_x (seq.head dummy_pt (left_pts c)) in
  map (fun p => Build_vert_edge lx (p_y (fst p)) (p_y (snd p))) 
   (seq_to_intervals (left_pts c)).

Definition cell_safe_exits_right (c : cell) : seq vert_edge :=
  let lx := p_x (head dummy_pt (right_pts c)) in
  map (fun p => Build_vert_edge lx (p_y (fst p)) (p_y (snd p))) 
   (seq_to_intervals (rev (right_pts c))).


Fixpoint positive_Z_to_decimal_string (fuel : nat) (z : Z) :=
  match fuel with
  | O => ""%string
  | S p =>
    if (z =? 0)%Z then
       ""%string
    else
    let (q, r) := Z.div_eucl z 10 in
    append (positive_Z_to_decimal_string p q) 
    match r with
    | 0%Z => "0"%string
    | 1%Z => "1"%string
    | 2%Z => "2"%string
    | 3%Z => "3"%string
    | 4%Z => "4"%string
    | 5%Z => "5"%string
    | 6%Z => "6"%string
    | 7%Z => "7"%string
    | 8%Z => "8"%string
    | _%Z => "9"%string
    end
  end.

Definition Z_to_string (z : Z) :=
  if (z =? 0)%Z then
    "0"%string
  else if (z <? 0)%Z then
    append "-" 
       (positive_Z_to_decimal_string (S (Z.abs_nat (Z.log2_up (- z)))) (- z))
  else 
    (positive_Z_to_decimal_string (S (Z.abs_nat (Z.log2_up z))) z).

Definition positive_rational_to_approx_decimal_string (x : Q) : string :=
    let frac_part := 
        (((1000 * Qnum x) / Zpos (Qden x)) mod 1000)%Z in
    let frac_part_string := 
      if (frac_part =? 0)%Z then
         "000"%string
      else if (frac_part <? 10)%Z then
        append "00" (Z_to_string frac_part)
      else if (frac_part <? 100)%Z then
        append "0" (Z_to_string frac_part)
      else 
        (Z_to_string frac_part) in
     append (Z_to_string (Qnum x / Z.pos (Qden x))) 
         (append "." frac_part_string).

Compute positive_rational_to_approx_decimal_string 1000.

Definition Q_to_approx_decimal_string (x : Q) :=
  if Qeq_bool x 0 then
    "0.000"%string
  else if Qle_bool 0 x then
    positive_rational_to_approx_decimal_string x
  else
    append "-" (positive_rational_to_approx_decimal_string (-x)).

Definition display_edge (tr_x tr_y scale : Q) (e : edge) :=
  let process_coord tr scale v :=
    Q_to_approx_decimal_string (tr + scale * v) in
  let process_point p :=
    append (process_coord tr_x scale (p_x p))
       (append " " (process_coord tr_y scale (p_y p))) in
  append (process_point (left_pt e))
    (append " moveto
" (append (process_point (right_pt e)) " lineto
")).

Definition display_cell (tr_x tr_y scale : Q) (c : cell) :=
  display_edge tr_x tr_y scale
      {| left_pt := seq.head dummy_pt (left_pts c);
                  right_pt := seq.last dummy_pt (left_pts c) |}.

Definition example_edge_list : seq edge :=
  Bedge (Bpt (-2) (-1)) (Bpt 2 1) ::
  Bedge (Bpt (4 # 5) (-1 # 5)) (Bpt 2 1) ::
  Bedge (Bpt (4 # 5) (-1 # 5)) (Bpt (17 # 5) (-5 / 2)) ::
  Bedge  (Bpt (-2) (-1)) (Bpt (17 # 5) (-5 / 2)) :: nil.

Definition edge_cond (e : edge) :=
  Qlt_bool (p_x (left_pt e)) (p_x (right_pt e)).

Lemma example_edge_cond :
   forallb edge_cond example_edge_list = true.
Proof. easy. Qed.

Notation BOTTOM :=
  ({| left_pt := {| p_x := -3; p_y := -3|};
      right_pt := {| p_x := 4; p_y := -4|}|}).

Notation TOP :=
  ({| left_pt := {| p_x := -4; p_y := 2|};
      right_pt := {| p_x := 4; p_y := 3|}|}).

Definition example_bottom : edge :=
  Bedge (Bpt (-3) (-3)) (Bpt 4 (-4)).

Definition example_top : edge :=
  Bedge (Bpt (-4) 2) (Bpt 4 3).

Definition inside_box (p : pt) (bottom top : edge) :=
  negb (point_under_edge p bottom) &&
  point_strictly_under_edge p top &&
  (Qlt_bool (p_x (left_pt bottom)) (p_x p) &&
     Qlt_bool (p_x p) (p_x (right_pt bottom))) &&
  (Qlt_bool (p_x (left_pt top)) (p_x p) &&
     Qlt_bool (p_x p) (p_x (right_pt top))).

Lemma example_inside_box :
  forallb (fun e => inside_box (point e) example_bottom example_top)
     (edges_to_events example_edge_list) = true.
Proof. easy. Qed.

Definition example_start_event :=
  seq.head dummy_event (edges_to_events example_edge_list).

Compute start example_start_event example_bottom example_top.

Compute List.length
  (sc_open1 (start example_start_event example_bottom example_top)).
Compute 
  (lst_closed (start example_start_event example_bottom example_top)).

Definition all_open (s : scan_state) :=
  sc_open2 s ++ lst_open s :: sc_open1 s.

Definition all_closed (s : scan_state) :=
  lst_closed s :: sc_closed s.

Definition step1m1 :=
        (start example_start_event example_bottom example_top).

Definition step1 :=
    step (nth 1 (edges_to_events example_edge_list) dummy_event)
    step1m1.

Definition step2m1 := step1.

Definition step2 :=
    step (nth 2 (edges_to_events example_edge_list) dummy_event)
        step2m1.

Definition step3m1 := step2.

Definition step3 :=
    step (nth 3 (edges_to_events example_edge_list) dummy_event)
        step3m1.

Definition step4m1 := step3.

Compute (List.length (all_open step1m1), all_open step1m1).
Compute (List.length (all_open step1), all_open step1).
Compute (List.length (all_open step2), all_open step2).
Compute (List.length (all_open step3), all_open step3).

Compute (List.length (all_closed step1m1), all_closed step1m1).
Compute (List.length (all_closed step1), all_closed step1).
Compute (List.length (all_closed step2), all_closed step2).
Compute (List.length (all_closed step3), all_closed step3).
Compute step3.

Compute lst_closed step3.

Compute List.length (sc_closed (iter_list step 
  (seq.behead (edges_to_events example_edge_list)) (start (seq.head dummy_event (edges_to_events example_edge_list))
      example_bottom example_top))).

Compute List.length (edges_to_cells example_bottom example_top example_edge_list).


Open Scope string_scope.
Compute
concat "
"
("" ::
"START"  ::
"%!PS" ::
List.map
  (fun (e : edge) => (display_edge 300 400 50 e))
  (example_bottom :: example_top :: example_edge_list) ++
List.map
  (fun c : cell => display_cell 300 400 50 c)
  (edges_to_cells example_bottom example_top example_edge_list) ++
"
stroke
" ::
"END" :: nil).
