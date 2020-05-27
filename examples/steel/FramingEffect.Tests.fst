module FramingEffect.Tests

open Steel.Memory
open Steel.FramingEffect

let equiv_sl_implies (p1 p2:hprop) : Lemma
  (requires p1 `equiv` p2)
  (ensures p1 `sl_implies` p2)
  = admit()

let lemma_sl_implies_refl (p:hprop) : Lemma
  (ensures p `sl_implies` p)
  = equiv_sl_implies p p

let emp_unit_variant (#a:Type) (p:a -> hprop) : Lemma
   (ensures can_be_split_forall (fun x -> p x `star` emp) p)
  = admit()

open FStar.Tactics

let canon' (_:unit) : Tac unit =
  or_else (fun _ -> Steel.Memory.Tactics.canon())
          (fun _ -> fail "Could not prove slprop equivalence")

let rec slterm_nbr_uvars (t:term) : Tac int =
  match inspect t with
  | Tv_Uvar _ _ -> 1
  | Tv_App _ _ ->
    let hd, args = collect_app t in
    slterm_nbr_uvars hd + fold_left (fun n (x, _) -> n + slterm_nbr_uvars x) 0 args
  | Tv_Abs _ t -> slterm_nbr_uvars t
  // TODO: Probably need to check that...
  | _ -> 0

let solve_can_be_split (args:list argv) : Tac bool =
  match args with
  | [(t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> norm [delta_only [`%can_be_split]];
                     // If we have exactly the same term on both side,
                     // equiv_sl_implies would solve the goal immediately
                     or_else (fun _ -> apply_lemma (`lemma_sl_implies_refl))
                      (fun _ -> apply_lemma (`equiv_sl_implies);
                       norm [delta_only [
                              `%__proj__CM__item__unit;
                              `%__proj__CM__item__mult;
                              `%Steel.Memory.Tactics.rm;
                              `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                              `%fst; `%snd];
                            primops; iota; zeta];
                       canon' ()));
        true
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen

let solve_can_be_split_forall (args:list argv) : Tac bool =
  match args with
  | [_; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> ignore (forall_intro());
                     norm [delta_only [`%can_be_split_forall]];
                     or_else (fun _ -> apply_lemma (`lemma_sl_implies_refl))
                       (fun _ ->
                       apply_lemma (`equiv_sl_implies);
                       or_else (fun _ ->  flip()) (fun _ -> ());
                       norm [delta_only [
                              `%__proj__CM__item__unit;
                              `%__proj__CM__item__mult;
                              `%Steel.Memory.Tactics.rm;
                              `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                              `%fst; `%snd];
                            primops; iota; zeta];
                       canon' ()));
        true
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen

let rec solve_subcomp_post (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | App _ t ->
        let hd, args = collect_app t in
        if term_eq hd (quote annot_sub_post) then (focus (fun _ ->
          norm [delta_only [`%annot_sub_post]];
          // Assuming for now that the body will always be Steel
          // instead of SteelF, as we'll lift pure to Steel by
          // a polymonadic bind with Steel alloc/read/...
          // That means the postcondition of return will be ?u_ret * ?u_emp
          apply_lemma (`emp_unit_variant)
          ))
        else (later());
        solve_subcomp_post tl
    | _ -> later(); solve_subcomp_post tl


let rec solve_triv_eqs (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
      let lnbr = slterm_nbr_uvars l in
      let rnbr = slterm_nbr_uvars r in
      // Only solve equality if there is only one uvar
      if lnbr = 0 || rnbr = 0 then trefl () else later();
      solve_triv_eqs tl
    | _ -> later(); solve_triv_eqs tl

// Returns true if the goal has been solved, false if it should be delayed
let solve_or_delay (g:goal) : Tac bool =
  let f = term_as_formula' (goal_type g) in
  match f with
  | App _ t ->
      let hd, args = collect_app t in
      if term_eq hd (quote delay) then false
      else if term_eq hd (quote can_be_split) then solve_can_be_split args
      else if term_eq hd (quote can_be_split_forall) then solve_can_be_split_forall args
      else false
  | Comp (Eq _) l r ->
    let lnbr = slterm_nbr_uvars l in
    let rnbr = slterm_nbr_uvars r in
    // Only solve equality if one of the terms is completely determined
    if lnbr = 0 || rnbr = 0 then (trefl (); true) else false
  | _ -> false


// Returns true if it successfully solved a goal
// If it returns false, it means it didn't find any solvable goal,
// which should mean only delayed goals are left
let rec pick_next (l:list goal) : Tac bool =
  match l with
  | [] -> false
  | a::q -> if solve_or_delay a then true else (later (); pick_next q)

let rec resolve_tac () : Tac unit =
  dump "all goals";
  match goals () with
  | [] -> ()
  | g ->
    if pick_next g then resolve_tac ()
    else
      (norm [delta_only [`%delay]];
      resolve_tac ())

[@@ resolve_implicits; framing_implicit]
let init_resolve_tac () : Tac unit =
  solve_triv_eqs (goals ());
  solve_subcomp_post (goals ());
  resolve_tac ()

assume val ref : Type0
assume val ptr (_:ref) : hprop u#1

assume val alloc (x:int)  : SteelT ref emp ptr
assume val free (r:ref) : SteelT unit (ptr r) (fun _ -> ptr r)
assume val read (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)

// AF: Tests 1 to 6 correctly solve all goals using the tactic
// They only fail because of errors such as
// Expected expression of type "star (ptr r) emp == star (ptr r) emp"; got expression "()" of type "unit"
// Failed while checking implicit ?434 set to () of expected type star (ptr r) emp == star (ptr r) emp
// Note that the equalities hold here, as one of the two terms always has been obtained
// through trefl
// This seems related to PR 2041

[@expect_failure]
let test1 (x:int) : SteelT ref emp ptr =
  let y = alloc x in y

// #set-options "--debug Steel.Effects2.Tests --debug_level Extreme --debug_level Rel --debug_level LayeredEffectsEqns --print_implicits --ugly --debug_level TwoPhases --print_bound_var_types"
[@expect_failure]
let test2 (r:ref) : SteelT int (ptr r) (fun _ -> ptr r) =
  let x = read r in
  x

[@expect_failure]
let test3 (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)
  = let x = read r in
    let y = read r in
    x

[@expect_failure]
let test4 (r:ref) : SteelT ref (ptr r) (fun y -> ptr r `star` ptr y)
  = let y = alloc 0 in
    y

[@expect_failure]
let test5 (r1 r2:ref) : SteelT ref (ptr r1 `star` ptr r2) (fun y -> ptr r1 `star` ptr r2 `star` ptr y)
  = let y = alloc 0 in
    y

[@expect_failure]
let test6 (r1 r2:ref) : SteelT unit (ptr r1 `star` ptr r2) (fun _ -> ptr r2 `star` ptr r1)
  = let _ = read r1 in
    ()


// Scoping issue to debug
[@expect_failure]
let test7 (a:unit) : SteelT ref emp (fun y -> ptr y) =
  let x = alloc 0 in
  let _ = read x in
  x



// [@@expect_failure]
// let test2 (r1 r2:ref) : SteelT (int & int) (ptr r1 `star` ptr r2) (fun _ -> ptr r1 `star` ptr r2) =
//   let x = read r1 in
//   let y = read r2 in
//   steel_ret (x, y)
