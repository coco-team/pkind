(*
This file is part of the Kind verifier

* Copyright (c) 2007-2011 by the Board of Trustees of the University of Iowa, 
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


(** Inductive process module *)

(** 
@author Temesghen Kahsai

*)

open Types
open Flags
open Exceptions
open Channels
open Globals
open Mpi
open Util


let solver = Globals.my_solver

(* Toss outputs *)
let toss x = () 

(* A variable used for printing inductive counter-example *)
let global_k = ref " "   


(** Single property verification *)
let singleProp sol = 
  let _ = debug_proc INDUCT_PROC None (" MAIN.") in 
  let induct_cex = ref " " in
  let switch_to_static_compression = ref false in
  let k_inc = ref sol.startdepth in
  let maxsteps = max !maxloops (sol.startdepth+1) in
  let local_firsttime = ref true in
  let firststep = ref true in
  let step_stop = ref false in
  let step_error = ref false in
  let _ = Kind_refine.set_num_abstract () in
  let _ = Kind_refine.set_not_fully_refined() in
  let refinement_pass = ref false in (* set to true if doing another pass 
                                        after refining *)
  let collected_newly_refined_vars = ref [] in
    
  (* force refinements after increasing periods *)
  (* for sal_ind mode, we force refinement if k > the set size *)
  let force_step_refinement k =
    let dif = k - (Kind_refine.get_last_k_refined()) in
      (dif > !force_refinement) || (k >= !force_refinement && k = maxsteps-1)
  in
    
  let _ = Kind_support.set_last_level_asserted (sol.startdepth-1) in
    
while  (!k_inc <= !Flags.maxloops && not !step_stop) do      
  let k = ref 0 in 
  let _ = if !more_steps then (
    let _ = debug_proc INDUCT_PROC None (" More steps (i.e., K > 1)") in
      k := !k_inc + (!k_step_size - 2); 
  )else( k := !k_inc;) in
    
  let k1 = !k-1 in
  let k_s = string_of_int !k in
   
    if not !refinement_pass then
      begin (* not refinement_pass *)
	debug_proc INDUCT_PROC None " not refinement_pass.";
        (* handle assertions *)	
        if Lus_assertions.assertions_present() then
          begin (* handle assertions *)
	    debug_proc INDUCT_PROC None  (" has assertions");	
            print_to_solver2 (
              Lus_convert_yc.simple_command_string
                (ASSERT(
                   F_PRED(solver#get#assertions,
                          [PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*(!k)))])
                 )));
            if !local_firsttime then
              for i= 0 to !k do
                print_to_solver2 (
                  Lus_convert_yc.simple_command_string
                    (ASSERT(
                       F_PRED(solver#get#assertions,
                              [PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))])
                     )));
		debug_proc INDUCT_PROC None  (" has assertions. Done.\n");
              done
          end; (* handle assertions *)
      end (* not refinement_pass *)
    else
      begin
        print_to_solver2 solver#get#safe_push; (* PUSH 2b *)
        print_to_solver2 (Lus_convert_yc.simple_command_string (QUERY(F_TRUE)))
      end; 

    (* we only go to k- step size *)
    List.iter (fun y ->
		 Kind_support.def_assert_initial sol.def_hash "DEF" sol.add y;
		 
		 for i=sol.startdepth to !k - !k_step_size do
		   Kind_support.persistent_step_single_assert sol.def_hash 
                     sol.startdepth sol.add STEP i y
		 done
              ) !collected_newly_refined_vars;
    
    collected_newly_refined_vars := [];

    let do_range = !local_firsttime || !k_step_size > 1 in
      if !loopfree_mode && static_path_compression.(step_abstr) then
        begin
          let startpoint =
            if !firststep then sol.startdepth
            else !k - sol.startdepth - !k_step_size
          in
            Kind_compression.general_compression_constraint sol.startdepth 
              sol.add print_to_solver2 startpoint (k1-sol.startdepth) sol.nvar 
        end;

      let perform_step_check = ref true in
      let previous_static_compression = ref static_path_compression.(step_abstr) in
      let initialize_step = ref true in
      let step_refined_vars = ref [] in
	
        while !perform_step_check do  (* step loop *)
          perform_step_check := false;
	  if iprobe any_source any_tag comm_world = None then
	    begin
	      let _ = debug_proc INDUCT_PROC (Some true) (" Checking K = "^k_s^ ". No message received.") in
	      if !initialize_step || not !previous_static_compression then
		begin (* setup step loop *)
                  initialize_step := false;
                  debug_proc INDUCT_PROC None " setup step loop - initialize step.";
                  if !loopfree_mode && not static_path_compression.(step_abstr) then
                    begin
                      try
                        if !switch_to_static_compression then
                          begin
                            switch_to_static_compression := false;
                            raise AllStatefulVarsRefined
                          end;

                        let header_string = 
                          solver#get#push_string^
                            (Lus_convert_yc.yc_state_vars_string_refined step_abstr)^"\n"
                        in
                        print_to_checker solver#get#push_string;
debug_proc INDUCT_PROC None ";4c";
                        print_to_solver2 header_string;
                        Kind_compression.abstracted_compression_constraint 
                          sol.startdepth sol.add print_to_solver2 0 (k1-sol.startdepth) 
                          sol.nvar ;
                      with NoStatefulVars -> 
debug_proc INDUCT_PROC None ";4e";
                       print_to_solver2 solver#get#push_string(***** PUSH *****) 
                      | AllStatefulVarsRefined ->
                        static_path_compression.(step_abstr) <- true;
                        Kind_compression.general_compression_constraint 
                          sol.startdepth sol.add print_to_solver2 0 (k1-sol.startdepth) 
                          sol.nvar ;
                        previous_static_compression := true;
debug_proc INDUCT_PROC None ";4f";
                        print_to_solver2 solver#get#push_string(***** PUSH *****)
                    end
                  else
                    begin
                      print_to_solver2 solver#get#push_string;(***** PUSH *****)
debug_proc INDUCT_PROC None ";4b ";
                      previous_static_compression := true
                    end;

                  (* generic terms *)
                  (* temporarily sol.add them since the last sol.startdepth *)
                  (* takes care of ite elim *)
                  for i=(!k-sol.startdepth) to (!k-1) do
                    if !var_defs_mode then
(**)                    Kind_support.def_assert_both2 sol.def_hash "DEF" 
                          [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))]
                          !k sol.from_checker_ch
                    else
                      begin
		
(**)                    print_to_solver2
                         (Lus_convert_yc.simple_command_string
                         (ASSERT(
                         F_PRED("DEF",[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))])
                         )))
                      end
                  done;
                  (* temporarily print all defs up from the last step up to 
                   k-sol.startdepth-1
                   this includes recently refined ones
                   remember that on the previous step we kept one step size *)
                  (* all skipped defs up to k-sol.startdepth-1 *)
                  if !k_step_size > 1 then
                    begin (* setup step loop *)
                      (* fill in for k_step_size > 1 *)
                      let startpoint,endpoint = 
                        if !firststep then
                          0,(!k-sol.startdepth)-1
                        else
                          !k - !k_step_size - sol.startdepth + 1, !k-sol.startdepth-1
                      in 
                      let defname = "DEF" in
                      for i=startpoint to endpoint do
                        if !var_defs_mode then
			  Kind_support.def_assert_both2 sol.def_hash defname 
                            [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))]
                            !k sol.from_checker_ch
                        else
                          begin
                            print_to_both2 
                              (Lus_convert_yc.simple_command_string
                              (ASSERT(
                               F_PRED(defname,[PLUS(POSITION_VAR(sol.nvar),
                                 NUM(sol.add*i))])
                              )))
                          end
                      done;
                    end;

                  if do_range then
                    begin
                      let startpoint = 
                        if !firststep then 1
                        else !k - !k_step_size + 1
                      in
                      for i=startpoint to (!k-1) do
                        print_to_solver2 
                          (Lus_convert_yc.simple_command_string
                          (ASSERT(
                           F_PRED("P",[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))])
                           )))
                      done
                    end;

                  (*Changed after discussion with Cesare i.e. _base is not needed*)
                
                print_to_solver2(Lus_convert_yc.simple_command_string(ASSERT(
                      F_NOT(F_PRED("P",[POSITION_VAR(sol.nvar)])))));
                end (* setup step loop *)
              else
                begin (* alt setup step loop *)
	               debug_proc INDUCT_PROC None "STEP : setup step loop - no initialize";
		
                print_to_checker solver#get#push_string;
		
            for i=(!k-sol.startdepth) to (!k-1) do
              if !var_defs_mode then
(**)                      Kind_support.def_assert_both2 sol.def_hash "DEF" 
                  [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))]
                  !k sol.from_checker_ch
              else
                begin
(**)               print_to_checker 
                    (Lus_convert_yc.simple_command_string
                       (ASSERT(
                        F_PRED("DEF",[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))])
                          )))
                end
            done;
            if !k_step_size > 1 then
              begin
                      (* fill in for k_step_size > 1 *)
                let startpoint,endpoint = 
                  if !firststep then
                    0,(!k-sol.startdepth)-1
                  else
                    !k - !k_step_size - sol.startdepth + 1, (!k-sol.startdepth)-1
                in 
                let defname = "DEF" in
                for i=startpoint to endpoint do
                  if !var_defs_mode then
(**)                        Kind_support.def_assert_both2 sol.def_hash defname 
                      [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))]
                      !k sol.from_checker_ch
                  else
                    begin
(**)                        print_to_checker 
                        (Lus_convert_yc.simple_command_string
                           (ASSERT(
                            F_PRED(defname,[PLUS(POSITION_VAR(sol.nvar),
						 NUM(sol.add*i))])
                              )))
                    end
                done
              end
		end;

            print_to_solver2 solver#get#safe_push; (* SAFE PUSH 1 *)
            print_to_solver2 (Lus_convert_yc.simple_command_string(QUERY(F_TRUE)));
            print_to_solver2 solver#get#done_string;


               
let out_step = solver#get#get_solver_output INDUCT_PROC sol.from_solver2_ch in
  if (solver#get#result_is_unsat out_step) then
    begin (* step valid *)  
      print_to_solver2 solver#get#safe_pop; (* SAFE PUSH 1 *)
      if !check_compression && !loopfree_mode 
        && not static_path_compression.(step_abstr) then
          begin
            debug_proc INDUCT_PROC None 
              (" Re-checking with full compression.\n");
            switch_to_static_compression := true;
            print_to_both2 solver#get#pop_string;
            (* sol.add the static def here *)
            initialize_step := true;
            perform_step_check := true
          end
      else 
        begin
	  debug_proc INDUCT_PROC (Some true) (" Sending 'VALID STEP'. ");
	  let validStep = VALID_STEP !k in
	    isend validStep base_proc 6 comm_world; 		
	    Globals.step_time_stop := (wtime());
	    step_stop := true
        end 
    end (* step valid *)
  else if (solver#get#result_is_sat out_step || solver#get#result_is_unknown out_step) then
    begin (* step invalid *)
      let go_to_next =
        (* if we refined, check this level again *)
        if !abs_mode &&
          Kind_refine.is_not_fully_refined step_abstr && 
          (Kind_refine.check_step_refinement !k) &&
          (solver#get#result_is_sat out_step) then
            begin (* step invalid abs *)
              let foundvars = 
                solver#get#get_cex INDUCT_PROC  out_step print_to_solver2 sol.from_solver2_ch 
              in
              let 
                  refinement_result = 
                           (* may POP stack *)
		debug_proc INDUCT_PROC None "check1";
                           print_to_solver2 solver#get#safe_pop;(* SAFE PUSH 1 *)
                           Kind_refine.check_and_refine_abstraction 
                             sol.from_checker_ch sol.def_hash sol.startdepth sol.add STEP 
                             foundvars sol.pvars !k
                         in
                         let previous_step_k = (!k-1) in
                         match refinement_result with
                           CHECK_IS_VALID ->
                             if force_step_refinement !k then
                               begin
                                 let ids_steps = 
                                   List.map (fun x -> (x,0)) sol.pvars 
                                 in
                                 debug_proc INDUCT_PROC None (" Forcing refinement.\n");
                                 (* may POP stack *)
                                 let xs = 
                                   Kind_refine.refine_abstraction 
                                     sol.from_checker_ch sol.def_hash sol.startdepth sol.add 
                                     false STEP foundvars !k ids_steps
                                 in
                                 step_refined_vars := List.rev_append 
                                   !step_refined_vars xs;

                                 if !previous_static_compression then
                                   print_to_checker solver#get#pop_string
                                 else
                                   begin
                                     initialize_step := true;
                                     print_to_solver2 solver#get#pop_string;
                                   end;
debug_proc INDUCT_PROC None("CHECK_IS_VALID");
                                 (* assert new vars *)
                                 List.iter (fun y ->
                                   (* assert up to sol.startdepth *)
                                   Kind_support.def_assert_initial sol.def_hash 
                                     "DEF" sol.add y;
                                   Kind_support.print_initialization_single 
                                     sol.def_hash sol.startdepth sol.add y;
                                (* assert from sol.startdepth to previous_step_k *)
                                   for i=sol.startdepth to previous_step_k do
                                     Kind_support.persistent_step_single_assert
                                       sol.def_hash sol.startdepth sol.add STEP i y
                                   done;
                                   (* assert in base up to k-1 *)
                                   if !Flags.only_1_abstraction then
                                   for i=sol.startdepth to (!k-1) do
                                     Kind_support.persistent_step_single_assert
                                       sol.def_hash sol.startdepth sol.add BASE i y
                                   done
                                 ) xs;
                                 false
                               end
                             else
                               true
                           | CHECK_IS_INVALID x ->
                             step_refined_vars := List.rev_append 
                               !step_refined_vars x;

                             if !previous_static_compression then
                               print_to_checker solver#get#pop_string
                             else
                               begin
                                 initialize_step := true;
                                 print_to_solver2 solver#get#pop_string
                               end;

debug_proc INDUCT_PROC None("CHECK_IS_INVALID");
                             (* assert new vars up to previous step *)
                             List.iter (fun y ->
                               (* assert up to sol.startdepth *)
                               Kind_support.def_assert_initial sol.def_hash "DEF" 
                                 sol.add y;
                               Kind_support.print_initialization_single 
                                 sol.def_hash sol.startdepth sol.add y;
                               for i=sol.startdepth to previous_step_k do
                               (* assert from sol.startdepth to previous_step_k *)
                                 Kind_support.persistent_step_single_assert 
                                   sol.def_hash sol.startdepth sol.add STEP i y
                               done;
                               (* assert in base up to k-1 *)
                               if !Flags.only_1_abstraction then
                               for i=sol.startdepth to (!k-1) do
                                 Kind_support.persistent_step_single_assert 
                                   sol.def_hash sol.startdepth sol.add BASE i y
                               done
                             ) x;
                             false (* also POP stack *)
                       end (* step invalid abs *)
                     else
                       begin
                         print_to_solver2 solver#get#safe_pop;(* SAFE PUSH 1 *)
                         true
                       end
                    in (* go_to_next done *)
                    if go_to_next then
                      begin (* step invalid continue *)
                        if solver#get#result_is_unknown out_step then
                          debug_proc INDUCT_PROC (Some true) (" Unknown in "^k_s^" steps. Continuing search.")
                        else
                          debug_proc INDUCT_PROC (Some true) (" Inductive step is Invalid at K = "^k_s^". Continuing search.");

(**)                    print_to_solver2 solver#get#pop_string; (***** POP *****)

                        if do_range then
                          begin
                            let startpoint = 
                              if !firststep then 1
                              else !k - !k_step_size + 1
                            in
                            for i=startpoint to !k-1 do
                              print_to_solver2 
                               (Lus_convert_yc.simple_command_string
                               (ASSERT(
                               F_PRED("P",[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))])
                               )))
                            done
                          end;

                          print_to_solver2 
                            (Lus_convert_yc.simple_command_string
                            (ASSERT(
                             F_PRED("P",[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*(!k)))])
                             )));

                          (* do permanent step asserts *)
                          let startpoint =
                            if !firststep then sol.startdepth
                            else !k - !k_step_size + 1
                          in
                          (* assert all from stepsize to k-1 *)
                          for i=startpoint to !k - 1 do
                            Kind_support.asserts_inductive
                              sol.def_hash sol.startdepth sol.add i sol.from_checker_ch
                          done;
                          (* presistent asserts of refined vars *)
                          List.iter (fun y ->
                            Kind_support.def_assert_initial sol.def_hash "DEF" sol.add y;
                            Kind_support.print_initialization_single sol.def_hash 
                              sol.startdepth sol.add y;
                            if !Flags.only_1_abstraction then
                            for i=sol.startdepth to (!k-1) do
                              Kind_support.persistent_step_single_assert 
                                sol.def_hash sol.startdepth sol.add BASE i y
                            done;
                            for i=sol.startdepth to startpoint-1 do
                              Kind_support.persistent_step_single_assert 
                                sol.def_hash sol.startdepth sol.add STEP i y
                            done
                          ) !step_refined_vars;
                          (* assert all at k *)
                          Kind_support.asserts_inductive sol.def_hash sol.startdepth sol.add !k sol.from_checker_ch;
                          local_firsttime := false;
                          firststep := false;
			  (* Print the current inductive counterexample *)
		    if (!Flags.inductive_cs) then (
		    let foundvars = solver#get#get_countermodel out_step print_to_solver2 sol.from_solver2_ch in
		    induct_cex := Kind_support.save_countermodel foundvars 0 k1; 
		    global_k := k_s;
		    );
                          k_inc := !k_inc + (!k_step_size)
                      end (* step invalid continue *)
                    else (* re-do step *)
                      begin
                        perform_step_check := true
                      end
                  end (* step invalid *)
                else
                  begin
                    debug_proc INDUCT_PROC (Some true) (" Abort in "^k_s^" step.");
                    if (solver#get#result_is_error out_step) then
                    debug_proc INDUCT_PROC None (" OUTPUT: "^out_step);
                    step_error := true;
                    step_stop := true
                  end

 end (* if - receive message check*)
	  else
	    begin
	      let msg = receive any_source any_tag comm_world in
		debug_proc INDUCT_PROC (Some true) "Received a message."; 
		match msg with 
		    STOP ->
		      begin 
			debug_proc INDUCT_PROC (Some true) "Received stop message from base process."; 
			Globals.step_time_stop := (wtime());
			step_stop := true
		      end
		    
		  | INV_FULL(invariant) -> 
		      begin
			debug_proc INDUCT_PROC (Some true) "Received an invariant.";
			debug_proc INDUCT_PROC None "Asserting invariant.";
			Kind_support.print_defs_to_solver2 sol.from_solver2_ch sol.from_checker_ch (invariant^"\n");
			debug_proc INDUCT_PROC None "Asserted Invariant.\n";
			
			for i= 0 to k1 do     
			  print_to_solver2 (
			    Lus_convert_yc.simple_command_string
                              (ASSERT(
				 F_PRED(solver#get#assertions_inv,
					[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))])
                               ))); 
			done; 
		      end

		  |  _ -> debug_proc INDUCT_PROC None ("Received wrong message.");
	               Globals.step_time_stop := (wtime());
		       
	    end    
        done; (* step loop *)
	
        refinement_pass := false;
        (* term check may break this *)
        if !incr_k_step_size then incr k_step_size;
done; (* main loop *)
    
    
    if (not !step_stop) && (!Flags.inductive_cs) then
      (
	let msg_to_base = STOP_INDUCT(!induct_cex, !global_k) in
	  send msg_to_base base_proc 10 comm_world;
      ) else  if (not !step_stop) then 
	send STOP base_proc 10 comm_world;
    Kind_refine.print_stats sol.def_hash
;;  


(** Initialization *)
let init_inductProc filename =
  let defdoc,maxdepth,def_hash,no_stateful,pvars, prop_list = Defgen.start filename in
  let add = Kind_support.get_add() in
  let nstart = solver#get#step_base_string in
  let nvar = solver#get#k_position_string in
  let startdepth = maxdepth + 1 in
  let from_checker_ch, from_solver2_ch = Kind_support.setup_solver2() in
 
   (* if no stateful vars, then cancels loopfree mode *)
    if no_stateful then( loopfree_mode := false; termination_check := false);
    if (!termination_check || !loopfree_mode) && not !abs_mode then (
      static_path_compression.(base_abstr) <- true;
      static_path_compression.(step_abstr) <- true);
    
    (* Needed for refinement*)
    if !checker_mode then print_to_checker solver#get#checker_setup_string;
    (* Print definitions *)
	let _ = Kind_support.print_defs_to_solver2 from_solver2_ch from_checker_ch (defdoc^"\n") in	  
	  { 
	    pvars = pvars;
	    add = add;
	    startdepth = startdepth;
	    nstart = nstart;
	    from_solver2_ch = from_solver2_ch;
	    from_solver_ch = dummy;
	    from_checker_ch = from_checker_ch;
	    cur_depth = maxdepth;
	    nvar= nvar;
	    def_hash = def_hash;
	    no_stateful = no_stateful;
	    prop_list = prop_list;
	    defdoc = defdoc
	  }
	    

(** Starting point for base proc*)
let main filename = 
  let sol = init_inductProc filename in
    (* If no multi is specified do only single property verification *)
    if !Flags.no_multi then (
      debug_proc INDUCT_PROC (Some true) "Single property verification by option no_multi.";
      singleProp sol
    )else (
    (* If only single property do single INDUCT, otherwise do multi  INDUCT (i.e. incremental verification)*)
    if List.length sol.prop_list == 1  then 
      ( debug_proc INDUCT_PROC (Some true) "Single property verification.";
	singleProp sol
      )else(
	debug_proc INDUCT_PROC (Some true) "Multiple property verification.";
	Multi_induct.main sol
      )
    )

