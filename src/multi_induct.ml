

(*
This file is part of the Kind verifier

* Copyright (c) 2007-2012 by the Board of Trustees of the University of Iowa, 
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


(** Inductive step process module for multiple properties *)

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
let toss x = () (* toss outputs *)
let global_k = ref " "  


let print_properties props k1= 
	if (List.length props == 1) then(
		print_to_solver2("(assert (not"); 
		List.iter(fun x -> print_to_solver2("("^x^" _n")) props;
		print_to_solver2(")))");
		print_to_solver2("\n");
	)else(
		print_to_solver2("(assert (not (and "); 
		List.iter(fun x -> print_to_solver2("("^x^" _n)")) props;
		print_to_solver2(")))");
		print_to_solver2("\n");
	)


let main sol = 
  let _ = debug_proc INDUCT_PROC None "MULTI: MAIN." in 
  let induct_cex = ref " " in
  let switch_to_static_compression = ref false in

  (* List of properties *)
  let var_prop =  List.map (fun x -> (Tables.get_varinfo_name x)) sol.pvars in
  let unsat_var_prop_list  = ref [] in
  let sat_var_prop_list  = ref [] in 
  let unsat_id_prop_list  = ref [] in
  let sat_id_prop_list  = ref [] in
  let unsolved_properties = ref [] in
  let prop_as_inv = ref [] in
  let inv_generated = ref [] in
  let invalid_prop_from_base = ref false in  (*to check if I recieve an invalid prop from base proc *)

  (* Initial list of properties*)
  let _ = unsolved_properties := var_prop in
  let _ = unsat_var_prop_list := var_prop in
  let _ = sat_var_prop_list := var_prop in
  let _ = unsat_id_prop_list := sol.pvars in
  let _ = sat_id_prop_list := sol.pvars in

  let k_inc = ref sol.startdepth in
  let local_firsttime = ref true in
  let firststep = ref true in
  let step_stop = ref false in
  let step_error = ref false in
  let done_message = ref false in

  let _ = Kind_support.set_last_level_asserted (sol.startdepth-1) in

  while (not !done_message) do

  while (!k_inc <= !Flags.maxloops && not !step_stop) do 
    let k = ref 0 in 	
	if !more_steps then (
	  debug_proc INDUCT_PROC None "MULTI: More steps (i.e., K > 1)";
	  k := !k_inc + (!k_step_size - 2))
	else
	  k := !k_inc;
	let k1 = !k-1 in
	let k_s = string_of_int !k in
	let _ = debug_proc INDUCT_PROC (Some true) ("MULTI: Checking K = "^k_s) in
	let do_range = !local_firsttime || !k_step_size > 1 in


	  (* handle assertions *)	
	  if Lus_assertions.assertions_present() then
	    begin (* handle assertions *)
	      let _ = debug_proc INDUCT_PROC None "MULTI: has assertions." in	
		print_to_solver2 (
		  Lus_convert_yc.simple_command_string
		    (ASSERT(F_PRED(solver#get#assertions,[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*(!k)))]))));
		if !local_firsttime then
		  for i= 0 to !k do
		    print_to_solver2 (
		      Lus_convert_yc.simple_command_string
			(ASSERT(F_PRED(solver#get#assertions,[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))]))));
		    debug_proc INDUCT_PROC None "MULTI: has assertions. DONE.";	
		  done
	    end; (* handle assertions *)

	  if !loopfree_mode && static_path_compression.(step_abstr) then
	    begin
	      let startpoint =
		if !firststep then sol.startdepth
		else !k - sol.startdepth - !k_step_size
	      in
		Kind_compression.general_compression_constraint sol.startdepth 
		  sol.add print_to_solver2 startpoint (k1-sol.startdepth) sol.nvar; 
	    end;
	  
	  let perform_step_check = ref true in
	  let initialize_step = ref true in
	  let previous_static_compression = ref static_path_compression.(step_abstr) in  
	    

	  while !perform_step_check && not(List.length !unsolved_properties == 0) do      
	    let _ = perform_step_check := false in  
	    if  iprobe any_source any_tag comm_world = None then
		 begin
		  let _ = debug_proc INDUCT_PROC (Some true) "MULTI: No message received." in
		  if (!invalid_prop_from_base) then
		    begin
		    	let _ = print_to_solver2("(reset)") in
		    	let _ = Kind_support.print_defs_to_solver2 sol.from_solver2_ch sol.from_checker_ch (sol.defdoc^"\n") in	 
		    	
				let _ = invalid_prop_from_base := false in
				let _ = debug_proc INDUCT_PROC None "MULTI: setup step loop - Initialize after receving invalid property from Base Case process." in
				let _ = print_to_solver2 solver#get#push_string in
			  	for i=0 to (!k-1) do
			    	if !var_defs_mode then
			      		Kind_support.def_assert_both2 sol.def_hash "DEF" [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))] !k sol.from_checker_ch
			    	else
						print_to_solver2
				  			(Lus_convert_yc.simple_command_string
				     			(ASSERT(F_PRED("DEF",[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))]))))
			  		done;
			  
			  	for i=1 to (!k-1) do
			    	List.iter( fun x -> print_to_solver2("(assert ("^ x ^ " (- _n "^string_of_int(i)^")))\n")) !unsolved_properties
			  	done;
			  
			    print_properties !unsolved_properties k1;
			
		    end  (* Restart after receving an invalid property *)

		  else
		    begin
			if !initialize_step || not !previous_static_compression then
			  begin (* setup step loop *)
			    let _ = initialize_step := false in
			    let _ = debug_proc INDUCT_PROC None "MULTI STEP PROC: setup step loop - Normal initialize step." in
			      if !loopfree_mode && not static_path_compression.(step_abstr) then
				begin
				  try
				    if !switch_to_static_compression then
				      begin
					switch_to_static_compression := false;
					raise AllStatefulVarsRefined
				      end;
				    
				    let header_string = solver#get#push_string^(Lus_convert_yc.yc_state_vars_string_refined step_abstr)^"\n" in
				      print_to_checker solver#get#push_string;
				      debug_proc INDUCT_PROC None ";4";
				      print_to_solver2 header_string;
				      Kind_compression.abstracted_compression_constraint sol.startdepth sol.add print_to_solver2 0 (k1-sol.startdepth) sol.nvar ;
				  with NoStatefulVars -> 
				    debug_proc INDUCT_PROC None ";4e";
				    print_to_solver2 solver#get#push_string(***** PUSH *****) 
				    | AllStatefulVarsRefined ->
					static_path_compression.(step_abstr) <- true;
					Kind_compression.general_compression_constraint sol.startdepth sol.add print_to_solver2 0 (k1-sol.startdepth) sol.nvar;
					previous_static_compression := true;
					debug_proc INDUCT_PROC None ";4f";
					print_to_solver2 solver#get#push_string(***** PUSH *****)
				end
			      else
				begin
				  print_to_solver2 solver#get#push_string;(***** PUSH *****)
				  debug_proc INDUCT_PROC None ";4b";
				  previous_static_compression := true
				end;
			      
			      for i=(!k-sol.startdepth) to (!k-1) do
				if !var_defs_mode then
				  Kind_support.def_assert_both2 sol.def_hash "DEF" [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))] !k sol.from_checker_ch
				else(
				    print_to_solver2
				      (Lus_convert_yc.simple_command_string
					 (ASSERT(F_PRED("DEF",[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))]))))
				   	)
			      done;
			      
			      (* Adding properties as invariants if any *)
			      if(!Flags.prop_as_invariant && (List.length !prop_as_inv !=0)) then
				(
				  debug_proc INDUCT_PROC (Some true) "MULTI: PROPERTY AS INVARIANTS.";
				  List.iter( fun x -> print_to_solver2("(assert ("^ x ^ " (+ _n 0)))\n")) !prop_as_inv;
				  for j=1 to (!k-1) do
				    List.iter( fun x -> print_to_solver2("(assert ("^ x ^ " (- _n "^string_of_int(j)^")))\n")) !prop_as_inv
				  done 	   
				);
			      
			   if do_range then
				begin
				  let startpoint = if !firststep then 1 else !k - !k_step_size + 1 in
				    for i=startpoint to (!k-1) do
				      List.iter( fun x -> print_to_solver2("(assert ("^ x ^ " (- _n "^string_of_int(i)^")))\n")) !unsolved_properties
				    done
				end;
			    
			    print_properties !unsolved_properties k1;
			  end (* setup step loop *) 
			else
			  begin (* alt setup step loop *)
			    let _ = debug_proc INDUCT_PROC None "MULTI STEP PROC : setup step loop - no initialize." in
			    let _ = print_to_checker solver#get#push_string in
			      
			      for i=(!k-sol.startdepth) to (!k-1) do
				if !var_defs_mode then
				  Kind_support.def_assert_both2 sol.def_hash "DEF" [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))] !k sol.from_checker_ch
				else
				  begin
				    print_to_checker(Lus_convert_yc.simple_command_string
						       (ASSERT(F_PRED("DEF",[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))]))))
				  end
			      done;
			      if !k_step_size > 1 then
				begin
				  (* fill in for k_step_size > 1 *)
				  let startpoint,endpoint = 
				    if !firststep then 0,(!k-sol.startdepth)-1
				    else
				      !k - !k_step_size - sol.startdepth + 1, (!k-sol.startdepth)-1 in 
				  let defname = "DEF" in
				    for i=startpoint to endpoint do
				      if !var_defs_mode then
					Kind_support.def_assert_both2 sol.def_hash defname [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))] !k sol.from_checker_ch
				      else
					begin
					  print_to_checker (Lus_convert_yc.simple_command_string
							      (ASSERT(F_PRED(defname,[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))]))))
					end
				    done
				end
			  end
		      end;
		    
		    let _ = print_to_solver2 solver#get#safe_push in
		    let _ = print_to_solver2 (Lus_convert_yc.simple_command_string(QUERY(F_TRUE)))in
		    let _ = print_to_solver2 solver#get#done_string in


		    let out_step = solver#get#get_solver_output INDUCT_PROC sol.from_solver2_ch in
		      if (solver#get#result_is_unsat out_step) then
			begin (* step valid *)  
			  let _ = debug_proc INDUCT_PROC (Some true) "MULTI: Valid inductive step." in
			  let _ = print_to_solver2 solver#get#safe_pop in (* SAFE PUSH 1 *)
			    if !check_compression && !loopfree_mode && not static_path_compression.(step_abstr) then
			      begin
				debug_proc INDUCT_PROC None "MULTI: Re-checking with full compression.";
				switch_to_static_compression := true;
				print_to_solver2 solver#get#pop_string;
				initialize_step := true;
				perform_step_check := true 
			      end
			    else 
			      begin
					let _ = debug_proc INDUCT_PROC (Some true) "MULTI: Sending valid property list -> [" in
				  	List.iter(fun x -> debug_proc INDUCT_PROC (Some true) (x^" ")) !unsolved_properties;
				  	debug_proc INDUCT_PROC (Some true) ("] to Base Case process at K = "^string_of_int(!k)^"\n");
				  
				  	let valid_prop_list = M_STEP_VALID(!unsolved_properties,!inv_generated, !prop_as_inv, !k) in
				   	 isend valid_prop_list base_proc 6 comm_world;
				     Globals.step_time_stop := (wtime());
				     step_stop := true;
			      end 
			end (* step valid *)

		      else if (solver#get#result_is_sat out_step || solver#get#result_is_unknown out_step) then
			begin (* step invalid *)
			  if solver#get#result_is_unknown out_step then
			    debug_proc INDUCT_PROC (Some true) ("MULTI: Inductive step is Unknown in "^k_s^" steps. Continuing search.")
			  else
			    debug_proc INDUCT_PROC (Some true) ("MULTI: Inductive step is Invalid at K ="^k_s^". Continuing search.");
			  
			  let foundvars = solver#get#get_cex INDUCT_PROC out_step print_to_solver2 sol.from_solver2_ch in
			  let simulation_value_hash = solver#get#get_simulation_cex INDUCT_PROC out_step print_to_solver2 sol.from_solver2_ch  in
			  let value_n = (Hashtbl.find simulation_value_hash ("_n")) in
			    
			  (* Update properties *)
			  let _ = 	
			    unsat_id_prop_list := 
			      List.filter (fun id -> Multi_prop_util.is_false 
					     (Hashtbl.find foundvars (id,int_of_string(value_n)))) !unsat_id_prop_list in
			  let _ = sat_id_prop_list := 
			    List.filter (fun id -> Multi_prop_util.is_true 
					   (Hashtbl.find foundvars (id,int_of_string(value_n)))) !sat_id_prop_list in	
			  let _ = unsat_var_prop_list := List.map (fun x -> (Tables.get_varinfo_name x)) !unsat_id_prop_list in
			  let _ = sat_var_prop_list :=  List.map (fun x -> (Tables.get_varinfo_name x)) !sat_id_prop_list in
			    
			  let _ = debug_proc INDUCT_PROC None ("SAT Properties at K = "^k_s) in 
			    debug_prop_var INDUCT_PROC !unsat_var_prop_list;
			    let _ = debug_proc INDUCT_PROC None ("UNSAT Properties at K = "^k_s) in
			      debug_prop_var INDUCT_PROC !sat_var_prop_list;
			      debug_proc INDUCT_PROC None "MULTI: Done Updating list of properties.";
			      
			      if (List.length(!sat_var_prop_list)!=0) then
				begin (* extra checking *)
				  let _ = debug_proc INDUCT_PROC (Some true) "MULTI: Indipendent check of some properties." in
				  let real_unsat, new_unsat_list =  
				    Extra_checks.induct_check sol !sat_var_prop_list !inv_generated !prop_as_inv k in 
				    if (real_unsat) then
				      begin
					let _ = debug_proc INDUCT_PROC None "MULTI: Indipendent check done. TRUE UNSAT" in
					let _ = unsolved_properties := List.filter(fun x ->  not (List.mem x new_unsat_list)) !unsolved_properties in
					  let _ = unsat_var_prop_list := !unsolved_properties in
					  let _ =sat_var_prop_list :=   !unsolved_properties in
					  let _ =unsat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) !unsat_var_prop_list in
					  let _ = sat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) !sat_var_prop_list in
					    
					  debug_proc INDUCT_PROC (Some true) "MULTI: Sending valid prop list -> [";
					  List.iter(fun x -> debug_proc INDUCT_PROC (Some true) (x^" ")) new_unsat_list;
					  debug_proc INDUCT_PROC (Some true) ("] to BASE PROC.");
					  
					  let _ = prop_as_inv := List.append !prop_as_inv new_unsat_list in      
					  let valid_prop_list = M_STEP_VALID(new_unsat_list, !inv_generated, !prop_as_inv, !k) in
					    isend valid_prop_list base_proc 6 comm_world;()	   
				      end
				    else
				      begin
					debug_proc INDUCT_PROC None "MULTI: Indipendent check done. FALSE UNSAT";
					unsat_var_prop_list := !unsolved_properties;
					sat_var_prop_list :=   !unsolved_properties;
					unsat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) !unsat_var_prop_list;
					sat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) !sat_var_prop_list;
				      end;
				end(* extra checking *)
			      else
				begin
				  debug_proc INDUCT_PROC (Some true) "MULTI: Indipendent Check is NOT needed.";
				end;
			    let _ = print_to_solver2 solver#get#pop_string in
			    let startpoint =  
					if !firststep then 1 else !k - !k_step_size + 1 in
						for i=startpoint to !k-1 do
				  			List.iter( fun x -> print_to_solver2("(assert ("^ x ^ "(- _n "^(string_of_int i)^")))\n")) !unsolved_properties;
						done;
				let _ = List.iter( fun x -> print_to_solver2("(assert ("^ x ^ "(- _n "^(string_of_int !k)^")))\n")) !unsolved_properties in 
				  
				(* do permanent step asserts *)
				let startpoint = if !firststep then sol.startdepth else !k - !k_step_size + 1 in
				  (* assert all from stepsize to k-1 *)
				  for i=startpoint to !k - 1 do
				    Kind_support.asserts_inductive sol.def_hash sol.startdepth sol.add i sol.from_checker_ch
				  done;
				  Kind_support.asserts_inductive sol.def_hash sol.startdepth sol.add !k sol.from_checker_ch;
				  local_firsttime := false;
				  firststep := false;
				  if (!Flags.inductive_cs) then (
				    let foundvars = solver#get#get_countermodel out_step print_to_solver2 sol.from_solver2_ch in
				      induct_cex := Kind_support.save_countermodel foundvars 0 k1; 
				      global_k := k_s;
				  );   
				  k_inc := !k_inc + (!k_step_size)
			end (* step invalid *)
		      else
			begin
			  (* STEP check = ERROR *)
			  debug_proc INDUCT_PROC (Some true) ("MULTI: Abort in "^k_s^" step.");
			  if (solver#get#result_is_error out_step) then
			    print_to_user_final ((Str.matched_string out_step)^"\n");
			  step_error := true;
			  step_stop := true
			end;
		end 

		(* ***************  RECIVIED A MESSAGE **************** *)
	    
	      else
		begin
		  let msg = receive any_source any_tag comm_world in
		  let _ =  debug_proc INDUCT_PROC (Some true) "MULTI: received a message." in 
		    match msg with 
			M_STEP_INVALID(invalid_prop) ->
			  begin 
			    let _ = invalid_prop_from_base := true in
			    let _ = debug_proc INDUCT_PROC None "MULTI: Invalid property [ " in
			    let _ = List.iter (fun x ->   debug_proc INDUCT_PROC None (x^" ")) invalid_prop in
			    let _ = debug_proc INDUCT_PROC None "] to be removed from the property list." in
			    let _ =  unsolved_properties := List.filter(fun x ->  not (List.mem x invalid_prop)) !unsolved_properties in
			    let _ = unsat_var_prop_list := List.filter(fun x ->  not (List.mem x invalid_prop)) !unsolved_properties in
			    let _ = sat_var_prop_list :=   List.filter(fun x ->  not (List.mem x invalid_prop)) !unsolved_properties in
			    let _ = unsat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) !unsat_var_prop_list in
			    let _ = sat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) !sat_var_prop_list in 
			      (*Check how many properties left *)
			      if (List.length !unsolved_properties == 0) then (step_stop:=true)
			  end
			    
		      | INV_FULL(invariant) -> 
			  begin
			    let _ = debug_proc INDUCT_PROC (Some true) "MULTI: Received an invariant." in		
			    let _ = Kind_support.print_defs_to_solver2 sol.from_solver2_ch sol.from_checker_ch (invariant^"\n") in
			    let _ = debug_proc INDUCT_PROC None "MULTI: DONE asserting received invariant" in
			    let _ = inv_generated := List.append !inv_generated [invariant] in
			      for i= 0 to k1 do     
				print_to_solver2 (
				  Lus_convert_yc.simple_command_string
				    (ASSERT(F_PRED(solver#get#assertions_inv,[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))])))); 
			      done; 	 
			  end
			    
		      | STOP ->
			  begin 
			    let _ = debug_proc INDUCT_PROC (Some true) "MULTI: STOP" in 
			      step_stop := true;
			      done_message := true
			  end
		      |  _ -> debug_proc INDUCT_PROC None "MULTI STEP PROC: Received wrong message.";
			   Globals.step_time_stop := (wtime());
		end
	    done; (* internal loop *)  
	    
	    if !incr_k_step_size then incr k_step_size;
    done; (* main loop *) 

    if (not !step_stop) && (!Flags.inductive_cs) then(
      	let msg_to_base = STOP_INDUCT(!induct_cex, !global_k) in
	  		send msg_to_base base_proc 10 comm_world;
    )else( 
      if (not !step_stop) then send STOP base_proc 10 comm_world);

	
	if not !done_message then(
		debug_proc INDUCT_PROC (Some true) ("MULTI: Waiting");
   		let msg = receive any_source any_tag comm_world in
   			match msg with 
		    	STOP ->
			  		begin 
			    		debug_proc INDUCT_PROC (Some true) "MULTI: STOP";
			      		Globals.step_time_stop := (wtime());
			      		done_message := true
			      	end
				| RECHECK(recheck_props) ->
			    	 begin
			     		debug_proc INDUCT_PROC (Some true) "MULTI: Rechecking properties:";
			     		debug_prop_var INDUCT_PROC recheck_props;
			     		print_to_solver2 solver#get#pop_string;
			     		unsolved_properties := recheck_props;
			     		step_stop := false;
			     	end
			 	| _ -> 
			    		debug_proc INDUCT_PROC None "MULTI STEP PROC: Received wrong message.";
			   			Globals.step_time_stop := (wtime());
		);   			
   		
done;
	 


 
 
 















