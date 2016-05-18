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


(** Base process module *)

(** 
@author Temesghen Kahsai

*)

open Types
open Flags
open Exceptions
open Channels
open Globals
open Mpi


(** Specific solver *)
let solver = Globals.my_solver
let toss x = ()  (* toss outputs *)

    
(**  For Abstraction/refinemnet *) 
let _ = Kind_refine.set_num_abstract () 
let _ = Kind_refine.set_not_fully_refined() 
let refinement_pass = ref false  (* set to true if doing another pass after refining *)
let newly_refined_vars = ref []  (* all vars refined this base k *)  
    
(** Defining some variables *)
let local_firsttime = ref true  
let final_position = 0  
let local_base_stop = ref false 


(** A process helper module*)
module HL = Proc_support.Helper 

(** Get the result from the solver*)
let get_bmc_result sol k =
  let k1 = k-1 in
  let k_s = string_of_int k in
  let out_base = solver#get#get_solver_output BASE_PROC sol.from_solver_ch in
    if (solver#get#result_is_unsat out_base) then
      begin (* base valid *)
	let _ = print_to_solver solver#get#safe_pop in
	let _ = debug_proc BASE_PROC (Some true) "Valid base." in
	let _ = print_to_solver solver#get#pop_string in
          (* re-assert the base defs for all newly refined vars *)
        let _ = 
	  List.iter (fun y ->
		       Kind_support.print_initialization_single sol.def_hash sol.startdepth sol.add y;
		       for i=sol.startdepth to k-1 do
			 Kind_support.persistent_step_single_assert sol.def_hash sol.startdepth 
			   sol.add BASE i y
		       done
		    ) !newly_refined_vars in
	  UNSAT
      end (* base valid *)	  
    else if (solver#get#result_is_sat out_base) then
      begin (* base invalid *)
	let _ = debug_proc BASE_PROC (Some true) "Invalid base." in
	let basestep = if !local_firsttime then BASE_INIT else BASE in
	let foundvars = solver#get#get_cex BASE_PROC out_base print_to_solver sol.from_solver_ch in
	let _ = debug_proc BASE_PROC None ("checking absmode "^(string_of_int (Kind_refine.get_num_abstract base_abstr))) in
	let _ = print_to_solver solver#get#safe_pop in
          if !abs_mode && Kind_refine.is_not_fully_refined base_abstr then
            begin
	      match Kind_refine.check_and_refine_abstraction sol.from_checker_ch 
		sol.def_hash sol.startdepth sol.add basestep foundvars sol.pvars k with
                    CHECK_IS_VALID -> () (* continue *)
                  | CHECK_IS_INVALID xs ->
		      (* assert new vars *)
		      List.iter (fun y ->
				   (* assert just y up to base step *)
				   Kind_support.print_initialization_single sol.def_hash 
				     sol.startdepth sol.add y;
				   (* assert just y from sol.startdepth to k-1 *)
				   for i=sol.startdepth to k-1 do
				     Kind_support.persistent_step_single_assert sol.def_hash 
				       sol.startdepth sol.add basestep i y
				   done
				) xs;
		      (* note these new vars *)
		      newly_refined_vars :=  List.rev_append (!newly_refined_vars) xs;
		      refinement_pass := true;
		      ()
            end
          else
            begin	       
	      let _ = debug_proc BASE_PROC None ("Invalid at K = "^k_s^".\n") in   
		HL.handle_cex foundvars k1
            end; 	
	  SAT
      end (* base invalid *)
    else
      begin
	print_to_user_final ("Abort in "^k_s^" base due to incompleteness or error.\n");
	if (solver#get#result_is_error out_base) then
          print_to_user_final ((Str.matched_string out_base)^"\n");
        let _ = debug_proc BASE_PROC None ("SOLVER OUTPUT: "^out_base) in
	  Globals.base_time_stop := (wtime());
	  ERROR
      end

(** Prepare the transition system and the property (i.e., No message recivied) *)
let  mk_trans_and_prop sol k_inc first_time_n_values =
  let k = !k_inc in
  let k1 = k-1 in
  let k_s = string_of_int k in
  let _ = debug_proc BASE_PROC (Some true) ("Checking K = "^k_s^". No message received.") in
    if not !refinement_pass then
      begin (* not refinement_pass *)
	let _ = debug_proc BASE_PROC None "not refinement_pass" in	 
	let _ =
	  if Lus_assertions.assertions_present() then
	    begin
	      let _ = debug_proc BASE_PROC None "Has assertion." in
		if !local_firsttime then (		
		  for i= 0 to k do
		    print_to_solver (Lus_convert_yc.simple_command_string(ASSERT(F_PRED(solver#get#assertions,[NUM(sol.add*i)]))));
		  done
		) else (
		  print_to_solver (Lus_convert_yc.simple_command_string(ASSERT(F_PRED(solver#get#assertions,[NUM(sol.add*k)]))))
		);
		debug_proc BASE_PROC None "Has assertions. Done. ";
	    end 
	in
	let _ = print_to_solver solver#get#push_string in
	  
        (* Assert the properties here*)
        let impl_premise = F_EQ(POSITION_VAR(sol.nstart),NUM(sol.add*k1),L_INT) in
        let impl_result = 
	  if !local_firsttime && k > 1 then (
              List.fold_left (fun acc x -> F_AND(F_PRED("P",[NUM(sol.add*x)]), acc)) (F_PRED ("P",[NUM(0)])) first_time_n_values
          )else (
            F_PRED("P",[NUM(final_position)]))
        in
        let _ = print_to_solver(Lus_convert_yc.simple_command_string (ASSERT(F_NOT(F_IMPL(impl_premise,impl_result))))) in
        let _ = print_to_solver solver#get#safe_push  in
          print_to_solver ( Lus_convert_yc.simple_command_string (QUERY(F_TRUE)))
      end (* not refinement_pass *)
    else
      begin
        let _ = print_to_solver solver#get#safe_push in
          print_to_solver (Lus_convert_yc.simple_command_string (QUERY(F_TRUE)))
      end;
    print_to_solver solver#get#done_string;
    k



(** Single property verification *)
let singleProp sol = 
  (* Print initial case *)
  let _ = print_to_solver solver#get#push_string in
  let _ = Kind_support.print_initialization sol.def_hash sol.startdepth sol.add sol.from_checker_ch in
  let k_inc = ref sol.startdepth in
  let first_time_n_values = (Array.to_list (Array.init (!k_inc-1) (fun x -> x+1))) in
   
    (*k-induction loop*)
    while (not !local_base_stop) do
      let _ = debug_proc BASE_PROC None "MAIN LOOP." in 
	if iprobe step_proc any_tag comm_world = None then
	  begin
	    let k = mk_trans_and_prop sol k_inc first_time_n_values in
	    let result_bmc = get_bmc_result sol k in
	      match result_bmc with 
		  SAT -> 
		    local_base_stop := true
		|UNSAT ->
		   if !local_firsttime then (
		     List.iter (fun x -> print_to_solver(Lus_convert_yc.simple_command_string(ASSERT(F_PRED("P",[NUM(sol.add*(x+1))]))))) (0::first_time_n_values)
		   ) else (
		     print_to_solver(Lus_convert_yc.simple_command_string(ASSERT(F_PRED("P",[NUM(sol.add*k)]))))
		   );
		    Kind_support.persistent_step_asserts_concrete sol.def_hash sol.startdepth sol.add k sol.from_checker_ch;
		    refinement_pass := false;
		    local_firsttime := false;
		    incr k_inc
		  
		|ERROR ->
		   local_base_stop := true
	  end
	else 

(****                   Received a message from Induct Proc          *********)
     begin
	let _ = debug_proc BASE_PROC (Some true) "Received message from the inductive process.\n" in
	let new_k = receive step_proc any_tag comm_world in
	  match new_k with
	      VALID_STEP kappa -> 
		begin
		    if (kappa >= !k_inc) then
		    begin
		      let _ = debug_proc BASE_PROC (Some true) "Extra checks are needed." in
		      let _ = debug_proc BASE_PROC (Some true) ("K received = "^(string_of_int kappa) ^ " -- Current K = " ^(string_of_int !k_inc)^ " \n") in
			let result = Extra_checks.single_bmc kappa !k_inc sol in
			let _ = debug_proc BASE_PROC (Some true) "Done with extra checks" in
			  if result then (HL.handle_valid kappa); 
			  local_base_stop := true;
		    end
		  else 
		    begin
		      HL.handle_valid kappa;
		      local_base_stop := true
		    end; 
		end
	      | STOP ->
		  begin
		    HL.handle_induct_cex None;
		    local_base_stop := true
		  end
	      | STOP_INDUCT(induct_cex,global_k) ->
		  begin
		    HL.handle_induct_cex (Some(induct_cex,global_k));
		    local_base_stop := true
		  end
	      |  _ -> assert false
	end;
    (*Check timeout*)
	if ((wtime()) -. !Globals.base_time_start) >= !Flags.timeout then (
	  let _ = Globals.base_time_stop := (wtime()) in
	  let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
	  let bt_string = string_of_float base_time in 
	  let property = Lus_convert_print.mk_property_string !Globals.prop_typed_stream in
	  if !Flags.xml then (
	    print_xml(Kind_support.print_resultProp_xml 
		    {result=TIMEOUT;
		     foundvars= None;
		     minstep=None;
		     maxstep=None;
		     induct_cex= None;
		     name= property;
		     k=string_of_int !k_inc;
		     time=bt_string}));
	  print_to_user_final("\n\n+++     TIMEOUT  +++\n\n");
	  if !Flags.mpi_abort then
	    (     
	      mpi_abort();
	    )else(
	      let _ = isend STOP step_proc 10 comm_world in
	      let _ = proc_size ==2 or ( debug_proc BASE_PROC (Some true) "Sent a message to INV GEN";isend STOP 2 9 comm_world;true) in
		local_base_stop := true);
	);
    done (* main loop *)


(** Initialization *)
let init_baseProc filename =
  let defdoc,maxdepth,def_hash,no_stateful,pvars,prop_list = Defgen.start filename in
  let add = Kind_support.get_add() in
  let nstart = solver#get#step_base_string in
  let startdepth = maxdepth + 1 in
  let from_checker_ch, from_solver_ch = Kind_support.setup_solver1() in
 
   (* if no stateful vars, then cancels loopfree mode *)
    if no_stateful then( loopfree_mode := false; termination_check := false);
    if (!termination_check || !loopfree_mode) && not !abs_mode then (
      static_path_compression.(base_abstr) <- true;
      static_path_compression.(step_abstr) <- true);
 
    (* Needed for refinement*)
    if !checker_mode then print_to_checker solver#get#checker_setup_string;
(* Print definitions *)
    let _ = Kind_support.print_defs_to_solver1 from_solver_ch from_checker_ch (defdoc^"\n") in	  
	  { 
	    pvars = pvars;
	    add = add;
	    startdepth = startdepth;
	    nstart = nstart;
	    nvar = "";
	    from_solver_ch = from_solver_ch; 
	    from_solver2_ch = dummy;
	    from_checker_ch = from_checker_ch;
	    cur_depth = maxdepth;
	    def_hash = def_hash;
	    no_stateful = no_stateful;
	    prop_list = prop_list;
	    defdoc = defdoc;
	  }
	    
	    
(** Starting point for base proc*)
let main filename = 
  let sol = init_baseProc filename in
    (* If no multi is specified do only single property verification *)
    if !Flags.no_multi then (
      debug_proc BASE_PROC (Some true) "Single property verification by option no_multi.";
      singleProp sol
    )else (
 (* If only single property do single BMC, otherwise do multi BMC (i.e. incremental verification)*)
    if List.length sol.prop_list == 1 then
      (debug_proc BASE_PROC (Some true) "Single property verification.";
       singleProp sol
      ) else (
	debug_proc BASE_PROC (Some true) "Multiple properties verification.";
	Multi_bmc.main sol
      )
    )

