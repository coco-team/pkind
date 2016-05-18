(*
This file is part of the Kind verifier

* Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

open Types
open Exceptions
open Channels
open Globals
open Mpi

let solver = Globals.my_solver

let refinement_steps = ref 0
(********************************************************************)
  let num_abstract =
    [| 0;0 |]

  let set_num_abstract () =
    num_abstract.(base_abstr) <-
      (Deftable.num_abstract_in_def_hash base_abstr);
    num_abstract.(step_abstr) <-
      (Deftable.num_abstract_in_def_hash step_abstr)

  let get_num_abstract x = num_abstract.(x)

  (* we do not change num_abstract when doing fine_core or hybrid *)
  (* when this reaches 0 we skip all further refinement checks *)
(********************************************************************)
  let not_fully_refined = [|false;false|]

  let set_not_fully_refined () = 
    not_fully_refined.(0) <- (num_abstract.(base_abstr) > 0); 
    not_fully_refined.(1) <- (num_abstract.(step_abstr) > 0)

  let is_not_fully_refined x = not_fully_refined.(x)
  
(********************************************************************)
  let skip_n_step_refinement_checks = ref 0 
  let step_refinement_count = ref 0 
  (* We increase this number if no refinements been needed in the last n 
     steps.  In other words, we will only periodically check step refinements
     if we have not done any refinements recently. *)


  let last_k_refined = ref 0(*startdepth*)

(********************************************************************)
  let get_last_k_refined () = !last_k_refined

  let check_fully_refined index =
    num_abstract.(index) <- num_abstract.(index) - 1;
    not_fully_refined.(index) <- (num_abstract.(index) > 0);
    if not (not_fully_refined.(index)) then
      print_to_user (solver#get#cc^"Abstraction fully refined.\n")

  let verify_fully_refined_hybrid startpoint index =
    (* this assumed check_fully_refined)( was already called *)
    if startpoint > 0 then
      num_abstract.(index) <- num_abstract.(index) + 1;
    not_fully_refined.(index) <- true

(********************************************************************)
  (* used to assign scores to variables' defhash entries *)
  let score_variables foundvars varlist k base_step from_checker_ch =
    let index = if base_step = STEP then 1 else 0 in
    List.iter (fun x ->
      if Abs.get_def_status x index = SUBTREE_DONE then
        Abs.set_def_score x 0 
      else
        begin
          let vars = x::(Abs.get_deplist x) in
          if Kind_support.check_for_bad_assignments from_checker_ch
             foundvars vars k
          then
            List.iter (fun y ->
              Abs.incr_def_score y) vars 
        end
    ) varlist

(********************************************************************)
  (* only check invalid step results with increasing periods *)
  let check_step_refinement k =
    let dif = k - !last_k_refined in
    if !Flags.no_inductive_check_mode then
      false
    else if dif < 2 then
      begin
        skip_n_step_refinement_checks := 0;
        step_refinement_count := 0;
        true
      end
    else if !step_refinement_count >= !skip_n_step_refinement_checks then
      begin
        incr skip_n_step_refinement_checks;
        step_refinement_count := 0;
        true
      end
    else
      begin
        incr step_refinement_count;
        false
      end

(********************************************************************)
  (* may POP context *)
  (* returns those actually refined *)
  let refine_abstraction from_checker_ch def_hash startdepth add is_forced 
  base_step foundvars k ids_steps =
    debug_to_user ("refine_abstraction k="^(string_of_int k)); 
    let k_s = string_of_int k in
    let k1 = k-1 in
    let base_step_str =
      if base_step = STEP then " step"
      else " base"
    in
    let index =
      if !Flags.only_1_abstraction then base_abstr
      else if base_step = STEP then step_abstr
      else base_abstr
    in
          begin
            let ids = List.map (fun (x,y)->x) ids_steps in
            print_to_user (solver#get#cc^k_s^base_step_str
              ^" is Invalid, refining abstraction ("^
              (string_of_int !refinement_steps)^").\n");
            if !Flags.print_dot_all then
              Deftable.print_curr_defhash_graph def_hash ids;

            if !Flags.fine_core_mode then (* level-specific refinement *)
            (* we do not change num_abstract, since we can't fully refine *)
              let next_unrefined =
                Abs.next_unrefined_fine_core_defs def_hash ids_steps
              in
              begin
                Globals.firsttime := false;
                match next_unrefined with
                    None ->
                      print_to_user 
                        (solver#get#cc^"Next refinement step not found.\n");
                      if base_step = STEP then 
                        raise No_next_refinement_step
                      else
                        begin
			   print_to_user_final("BASE PROC: Found COUNTEREXAMPLE at K ="^k_s^". Abstraction has been used.\n");
                          Kind_support.print_countermodel foundvars (-k1) 0;
			  Globals.base_time_stop := (wtime());
                            if !Flags.mpi_abort then
			    (mpi_abort();)
			  else
			    (
			      send STOP step_proc 8 comm_world;
			      Globals.base_stop := true )
                        end;
                      []
                  | Some x -> (* make sure we stay in this round *)
                      incr refinement_steps;
                      last_k_refined := k;
                      List.iter (fun (y,s) ->
                        let v = Tables.get_varinfo_name y in
                        print_to_user (solver#get#cc^"Refining "
                          ^(Tables.resolve_var_name v)^"("^(string_of_int s)
                          ^") in"^base_step_str^"\n")
                      ) x;
                      List.iter (fun (y,s) ->
                        (* print out assert for level s *)
                        Kind_support.persistent_step_single_level_assert 
                          def_hash startdepth add base_step s y k
                      ) x;
(* FIX THIS! *)
                      List.iter (fun (y) ->
                        let v = Tables.get_varinfo_name y in
                        print_to_user (solver#get#cc^"Refining "
                          ^(Tables.resolve_var_name v)^"("^(string_of_int k)
                          ^") in step\n")
                      ) (Abs.get_refined_step_as_well());
                      List.iter (fun (y) ->
                      (* print out assert for level s *)
                        Kind_support.persistent_step_single_level_assert 
                          def_hash startdepth add STEP k y k
                      ) (Abs.get_refined_step_as_well());
(* FIX THIS! *)
                      List.map (fun (y,_) -> y) x
              end
            else (* persistent refinement *)
              begin
                let next_unrefined = 
                  if !Flags.core_mode && is_forced then
                    Abs.next_unrefined_def def_hash ids index
                  else if !Flags.core_mode && is_forced then
                    Abs.next_unrefined_core_defs def_hash ids index
                  else if !Flags.full_subtree_mode then
                    Abs.next_unrefined_full_subtree def_hash ids index
                  else if !Flags.hybrid_core_mode then
                    Abs.next_unrefined_hybrid_core def_hash ids_steps index
                  else if !Flags.incr_mode then
                    Abs.next_unrefined_defs_incr def_hash ids index
                  else if !Flags.best_first_path_mode then
                    Abs.next_unrefined_def_bfpath def_hash index
                  else if !Flags.path_mode then
                    Abs.next_unrefined_def_path def_hash ids index
                  else if !Flags.hpath_mode then
                    begin
                      score_variables foundvars ids k base_step from_checker_ch;
                      let ids' = List.stable_sort (Abs.rev_compare_defs) ids in
                      Abs.next_unrefined_def_path def_hash ids' index
                    end
                  else if !Flags.hpath_mode1 then
                    Abs.next_unrefined_def_hpath true !Flags.rev_heuristic_mode
                      def_hash ids index
                  else if !Flags.hpath_mode2 then
                    Abs.next_unrefined_def_hpath false 
                      !Flags.rev_heuristic_mode 
                      def_hash ids index
                  else
                    Abs.next_unrefined_def def_hash ids index
                in
                match next_unrefined with
                    None -> 
                      print_to_user 
                        (solver#get#cc^"Next refinement step not found.\n");
                      if base_step = STEP then
                        (* this can happen with separate solvers *)
                        raise No_next_refinement_step 
                      else
                        begin
                        (*  print_to_user_final 
                            (solver#get#cc^k_s^" base is Invalid.\n"); *)
			  print_to_user_final("BASE PROC: Found COUNTEREXAMPLE at K ="^k_s^". Abstraction has been used\n");
                          Kind_support.print_countermodel foundvars 0 k1;
			  Globals.base_time_stop := (wtime());
			  let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
			  let bt_string = string_of_float base_time in 
			    print_to_user_final("BASE PROC Wall Time :- "^bt_string^"\n"); 
                          if !Flags.mpi_abort then
			    (mpi_abort();)
			  else
			    (
			      send STOP step_proc 8 comm_world;
			      Globals.base_stop := true )
                        end;
                      []
                  | Some x -> (* make sure we stay in this round *)
                      incr refinement_steps;
                      last_k_refined := k;
                      List.iter (fun y ->
                        let v = Tables.get_varinfo_name y in
                        print_to_user (solver#get#cc^"Refining "^
                          (Tables.resolve_var_name v)^" in"^base_step_str^"\n");
                        if !Flags.only_1_abstraction then
                          begin
                            check_fully_refined base_abstr;
                            check_fully_refined step_abstr
                          end
                        else
                          check_fully_refined index
                      ) x;
                      List.iter (fun y ->
                        let v = Tables.get_varinfo_name y in
                        print_to_user (solver#get#cc^"Refining "^
                          (Tables.resolve_var_name v)^" in step\n");
                        check_fully_refined step_abstr
                      ) (Abs.get_refined_step_as_well());
                      (* if we are in the initial set, we need to re-do
                         the initialization as well *)
                      if !Flags.hybrid_core_mode then
                        begin
                          (* take into asolver#get#ccount stuff *)
                          List.iter (fun y ->
                            Kind_support.print_initialization_single def_hash 
                              startdepth add y;
                            let startpoint,endpoint = 
                              try
                                match Hashtbl.find def_hash y with
                                    DEF_REF _ -> k,(k-1)
                                  | DEF_STR defline ->
                                      begin
                                        (* refined nums are neg, k is pos *)
                                        match defline.abstr.(index) with
                                            REFINED(z) ->
                                              if -z < k then
                                                (-z),(k-1)
                                              else
                                                k,(k-1)
                                          | REFINED_MORE(u,v)->
                                                (-v),(-u)
                                          | _ -> k,(k-1)
                                      end
                              with Not_found -> k,(k-1)
                            in
                            let sp = if startdepth > startpoint then 
                                       startdepth
                                     else
                                       startpoint
                            in
                            verify_fully_refined_hybrid sp index;
                            for i=sp to endpoint do
                      (* print out asserts for these vars up to the endpoint *)
                              Kind_support.persistent_step_single_assert 
                                def_hash startdepth add base_step i y
                            done
                          ) x
                        end;
                     x
              end
          end

(********************************************************************)
  let check_and_refine_abstraction from_checker_ch def_hash startdepth add base_step foundvars pvars k =
    debug_to_user ("check_and_refine_abstraction k="^(string_of_int k)); 
    let k_s = string_of_int k in
    let k1 = k-1 in
    try
      begin
        match 
          Kind_support.query_checker from_checker_ch foundvars base_step k1 
        with
            CHECK_VALID -> 
              begin
                if base_step = STEP then
                  begin
                    print_to_user (solver#get#cc^k_s^" step is Invalid.\n")
                  end
                else
                  begin
                   (* print_to_user_final (solver#get#cc^k_s^" base is Invalid.\n");*)
		     print_to_user_final("BASE PROC: Found COUNTEREXAMPLE at K ="^k_s^". Abstraction has been used.\n");
                    Kind_support.print_countermodel foundvars 0 k1;
		    Globals.base_time_stop := (wtime());
		    let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
		    let bt_string = string_of_float base_time in 
		      print_to_user_final("BASE PROC Wall Time :- "^bt_string^"\n"); 
                    if !Flags.mpi_abort then
			    (mpi_abort();)
			  else
			    (
			      send STOP step_proc 8 comm_world;
			      Globals.base_stop := true )
                  end
              end;
              CHECK_IS_VALID
          | CHECK_INCORRECT ids_steps -> (* may POP stack *)
              CHECK_IS_INVALID 
                (refine_abstraction from_checker_ch def_hash startdepth add false 
                   base_step foundvars k ids_steps)
      end
    with No_next_refinement_step ->
      let index = 
        if !Flags.only_1_abstraction then base_abstr
        else if base_step = STEP then step_abstr
        else base_abstr
      in
      if not_fully_refined.(index) then
        begin (* force refinement *)
          let ids_steps = List.map (fun x -> (x,k-1)) pvars in
          print_to_user (solver#get#cc^"Forcing refinement.\n");
          CHECK_IS_INVALID 
            (refine_abstraction from_checker_ch def_hash startdepth add true 
               STEP foundvars k ids_steps)
        end
      else
        raise No_next_refinement_step


(********************************************************************)
  let print_stats def_hash =
    (* print_to_user (solver#get#cc^"Variables used: "
      ^(string_of_int (Hashtbl.length (Tables.get_used_vars())))^"\n"); *)
    if !Flags.abs_mode && not !Globals.error then
      begin
        print_to_user (solver#get#cc^"Refinement steps: "
          ^(string_of_int !refinement_steps)
          ^"\n");
        if not_fully_refined.(base_abstr) || not_fully_refined.(step_abstr) then
          begin
            print_to_user (solver#get#cc^"The following variables were not refined in base:\n");
            Hashtbl.iter (fun x y -> match y with
                DEF_STR z -> if z.abstr.(base_abstr) = NOT_REFINED then
                             let v = Tables.get_varinfo_name x in
                             print_to_user (solver#get#cc^"  "
                               ^(Tables.resolve_var_name v)^"\n")
              | _ -> ()
            ) def_hash;
            print_to_user (solver#get#cc^"The following variables were not refined in step:\n");
            Hashtbl.iter (fun x y -> match y with
                DEF_STR z -> if z.abstr.(step_abstr) = NOT_REFINED then
                             let v = Tables.get_varinfo_name x in
                             print_to_user (solver#get#cc^"  "
                               ^(Tables.resolve_var_name v)^"\n")
              | _ -> ()
            ) def_hash
          end
        else
          print_to_user (solver#get#cc^"All variables were refined\n")
      end

