(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                Sadiq Jaffer, OCaml Labs Consultancy Ltd                *)
(*                                                                        *)
(*   Copyright 2020 OCaml Labs Consultancy Ltd                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Mach

module StringSet = Set.Make (String)

(* Add a poll test and polling instruction before [f]. In the later linearisation
   pass this will simplify in to a conditional and backwards jump pair *)
let add_fused_poll_before (f : Mach.instruction) : Mach.instruction =
  Mach.instr_cons
    (Iop Ipoll)
    [||] [||] f

(* Add a poll instruction which checks the young limit itself before [f] *)
let add_checked_poll_before _ (f : Mach.instruction) : Mach.instruction =
    Mach.instr_cons
      (Iop Ipoll)
      [||] [||] f

(* The result of a sequence of instructions *)
type path_result = WillPoll | NoPoll | Exited

(* The combined result of two sequences of instructions *)
let combine_paths p0 p1 =
  match (p0, p1) with
  (* both paths will poll, might not need to poll *)
  | WillPoll, WillPoll -> WillPoll
  (* one path exits without polling *)
  | Exited, _ | _, Exited -> Exited
  (* no polling happens in one of the paths *)
  | NoPoll, _ | _, NoPoll -> NoPoll

(* Check each sequence of instructions in the array [arr] and
   combine their allocation results *)
let rec reduce_paths_array ~future_funcnames arr =
  let rec red_arr acc arr n =
    match n with
    | 0 -> acc
    | _ ->
        let curr_path = check_path ~future_funcnames arr.(n) in
        let new_acc =
          match acc with
          | None -> curr_path
          | Some v -> combine_paths v curr_path
        in
        red_arr (Some new_acc) arr (n - 1)
  in
  let res = red_arr None arr (Array.length arr - 1) in
  match res with 
  | None -> NoPoll 
  | Some v -> v
(* Check each sequence of instructions in the list [l] and
   combine their allocation results *)
and reduce_paths_list ~future_funcnames l =
  let rec red_list acc l =
    match l with
    | [] -> acc
    | h :: tl ->
        let curr_path = check_path ~future_funcnames h in
        let new_acc =
          match acc with
          | None -> curr_path
          | Some v -> combine_paths v curr_path
        in
        red_list (Some new_acc) tl
  in
  let res = red_list None l in
  match res with None -> NoPoll | Some v -> v
(* Check a sequence of instructions from [f] and return whether
   they poll, don't poll or exit without polling *)
and check_path ~future_funcnames (f : Mach.instruction) : path_result =
  match f.desc with
  | Iifthenelse (_, i0, i1) -> (
      match combine_paths (check_path ~future_funcnames i0) (check_path ~future_funcnames i1) with
      | NoPoll -> check_path ~future_funcnames f.next
      | pv -> pv )
  | Iswitch (_, cases) -> (
      let case_state = reduce_paths_array ~future_funcnames cases in
      match case_state with NoPoll -> check_path ~future_funcnames f.next | pv -> pv )
  | Icatch (_, handlers, body) -> (
      let handlers_state =
        reduce_paths_list ~future_funcnames (List.map (fun (_, h) -> h) handlers)
      in
      match combine_paths handlers_state (check_path ~future_funcnames body) with
      | NoPoll -> check_path ~future_funcnames f.next
      | pv -> pv )
  | Itrywith (body, handler) -> (
      match combine_paths (check_path ~future_funcnames body) (check_path ~future_funcnames handler) with
      | NoPoll -> check_path ~future_funcnames f.next
      | pv -> pv )
  | Ireturn | Iop (Itailcall_ind _) -> Exited
  | Iop (Icall_imm { func; _ } | Itailcall_imm { func; _ }) ->
    if (StringSet.mem func future_funcnames) then
      (* this means we have a call to a function that might be a self call
         or a call to a future function (which won't have a poll) *)
      Exited
    else
      (* if we call a function already defined, we have already taken care of polling *)
      WillPoll 
  | Iend | Iexit _ -> NoPoll
  | Iop (Ialloc _) | Iraise _ -> WillPoll (* Iraise included here because
                                                it has a poll inserted *)
  | Iop _ -> check_path ~future_funcnames f.next

(* This determines whether from a given instruction we unconditionally
   allocate and this is used to avoid adding polls unnecessarily *)
let polls_unconditionally ~future_funcnames (i : Mach.instruction) =
  match check_path ~future_funcnames i with 
  | WillPoll -> true 
  | NoPoll | Exited -> false

(* returns a list of ids for the handlers of recursive catches from
   Mach instruction [f]. These are used to later add polls before
   exits to them. *)
let rec find_rec_handlers ~future_funcnames (f : Mach.instruction) =
  match f.desc with
  | Iifthenelse (_, ifso, ifnot) ->
      let ifso_rec_handlers = find_rec_handlers ~future_funcnames ifso in
      let ifnot_rec_handlers = find_rec_handlers ~future_funcnames ifnot in
      let next_rec_handlers = find_rec_handlers ~future_funcnames f.next in
      ifso_rec_handlers @ ifnot_rec_handlers @ next_rec_handlers
  | Iswitch (_, cases) ->
      let case_rec_handlers =
        Array.fold_left
          (fun agg_rec_handlers case ->
            agg_rec_handlers @ find_rec_handlers ~future_funcnames case)
          [] cases
      in
      case_rec_handlers @ find_rec_handlers ~future_funcnames f.next
  | Icatch (rec_flag, handlers, body) -> (
      match rec_flag with
      | Recursive ->
          let rec_handlers =
            List.map
              (fun (id, handler) ->
                let inner_rec_handlers = find_rec_handlers ~future_funcnames handler in
                let current_rec_handlers =
                  if not (polls_unconditionally ~future_funcnames handler) then [ id ] else []
                in
                inner_rec_handlers @ current_rec_handlers)
              handlers
            |> List.flatten
          in
          let body_rec_handlers = find_rec_handlers ~future_funcnames body in
          body_rec_handlers @ rec_handlers @ find_rec_handlers ~future_funcnames f.next
      | Nonrecursive ->
          let non_rec_catch_handlers =
            List.fold_left
              (fun tmp_rec_handlers (_, handler) ->
                tmp_rec_handlers @ find_rec_handlers ~future_funcnames handler)
              [] handlers
          in
          let body_rec_handlers = find_rec_handlers ~future_funcnames body in
          body_rec_handlers @ non_rec_catch_handlers @ find_rec_handlers ~future_funcnames f.next
      )
  | Itrywith (body, handler) ->
      let handler_rec_handler = find_rec_handlers ~future_funcnames handler in
      let body_rec_handlers = find_rec_handlers ~future_funcnames body in
      body_rec_handlers @ handler_rec_handler @ find_rec_handlers ~future_funcnames f.next
  | Iexit _ | Iend | Ireturn
  | Iop (Itailcall_ind _)
  | Iop (Itailcall_imm _)
  | Iraise _ ->
      []
  | Iop _ -> find_rec_handlers ~future_funcnames f.next

(* given the list of handler ids [rec_handelrs] for recursive catches, add polls before
   backwards edges starting from Mach instruction [i] *)
let instrument_body_with_polls (rec_handlers : int list) (i : Mach.instruction)
    =
  (* the [current_handlers] list allows for an optimisation which avoids putting a poll
    before the first jump in to a loop *)
  let rec instrument_body (current_handlers : int list) (f : Mach.instruction) =
    let instrument_with_handlers i = instrument_body current_handlers i in
    match f.desc with
    | Iifthenelse (test, i0, i1) ->
        {
          f with
          desc = Iifthenelse (test, instrument_with_handlers i0, instrument_with_handlers i1);
          next = instrument_with_handlers f.next;
        }
    | Iswitch (index, cases) ->
        {
          f with
          desc = Iswitch (index, Array.map instrument_with_handlers cases);
          next = instrument_with_handlers f.next;
        }
    | Icatch (rec_flag, handlers, body) ->
        {
          f with
          desc =
            Icatch
              ( rec_flag,
                List.map
                  (fun (idx, instrs) ->
                    (idx, instrument_body (idx :: current_handlers) instrs))
                  handlers,
                instrument_with_handlers body );
          next = instrument_with_handlers f.next;
        }
    | Itrywith (body, handler) ->
        {
          f with
          desc = Itrywith (instrument_with_handlers body, instrument_with_handlers handler);
          next = instrument_with_handlers f.next;
        }
    | Iexit id ->
        let new_f = { f with next = instrument_with_handlers f.next } in
        if List.mem id current_handlers && List.mem id rec_handlers then
          add_fused_poll_before new_f
        else new_f
    | Iend | Ireturn | Iop (Itailcall_ind _) | Iop (Itailcall_imm _)
      ->
        f
    | Iraise _ -> 
      add_checked_poll_before true { f with next = instrument_with_handlers f.next }
    | Iop _ -> { f with next = instrument_with_handlers f.next }
  in
  instrument_body [] i

let instrument_fundecl ~future_funcnames (i : Mach.fundecl) : Mach.fundecl =
  let f = i.fun_body in
  let rec_handlers = find_rec_handlers ~future_funcnames f in
  { i with fun_body = instrument_body_with_polls rec_handlers f }

let requires_prologue_poll ~future_funcnames (f : Mach.instruction) : bool =
  polls_unconditionally ~future_funcnames f