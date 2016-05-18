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

(** Base process module for multiple properties *)

(** 
@author Temesghen Kahsai

*)

open Types
open Flags
open Exceptions
open Channels
open Globals
open Mpi
open ExtString


let solver = Globals.my_solver
let toss x = () (* toss outputs *)
      
(* Function to check if an invalid properties is contained in the recivied message*)
let rec check_duplicates l1 l2 =
match l1, l2 with 
| [], [] -> []
| h1::t1, [] -> []
| [], h2::t2 -> []
| [h1], [h2] -> []
| [h1], h2::l2 -> if h1 = h2 then l2 else []
| h1::l1, h2::l2 -> if h1=h2 then (check_duplicates l1 l2) else (check_duplicates l1 (h2::l2))


(* Function to send STOP messages and print summaries*)
let make_notification valid_prop invalid_prop =
	Multi_prop_util.print_summary valid_prop invalid_prop;
	if !Flags.mpi_abort then(mpi_abort())
	else( 
		isend STOP step_proc 8 comm_world;
		proc_size ==2 or (debug_proc BASE_PROC (Some true) "MULTI: Sent a STOP message to INV GEN";isend STOP 2 9 comm_world;true);();
	)



(** A process helper module*)
module HL = Proc_support.Helper 

(* Main function *)
let main sol = 
  let _ = debug_proc BASE_PROC None "MULTI: MAIN LOOP." in
  let _ = debug_proc BASE_PROC None ("MULTI: Start depth: " ^ string_of_int (sol.startdepth) ) in
  let k_inc = ref sol.startdepth in
  let local_firsttime = ref true in 
    
  (* List of properties *)
  let position = POSITION_VAR (solver#get#position_var1) in 
  let parsed_multiple_prop  =  Lus_convert_yc.yc_multi_property_header_list position sol.prop_list in
  let var_prop = List.map (fun x -> String.strip ~chars:" " (Multi_prop_util.mk_name_property x)) parsed_multiple_prop in
  let named_prop = Multi_prop_util.create_new_named_list var_prop in
  let unsolved_prop_list = ref [] in
  let unsat_id_prop_list  = ref [] in
  let sat_id_prop_list  = ref [] in
  let unsat_var_prop_list  = ref [] in
  let sat_var_prop_list  = ref [] in 

  (*Collect the var of the invalid properties *)
  let invalid_var_prop = ref [] in
    
  (*Collection of valid/invalid properties (original names) *)
  let valid_properties = ref [] in
  let invalid_properties = ref [] in
    
  print_string ("<Results>\n");
  (* Initial list of properties*)
  let _ = unsolved_prop_list := var_prop in
  let _ = unsat_var_prop_list := var_prop in 
  let _ = sat_var_prop_list := var_prop in
  let _ = unsat_id_prop_list := sol.pvars in
  let _ = sat_id_prop_list := sol.pvars in
    
  let _ = print_to_solver solver#get#push_string in
  let _ = Kind_support.print_initialization sol.def_hash sol.startdepth sol.add sol.from_checker_ch in

  let base_error = ref false in
  let local_base_stop = ref false in

  (* For Abstraction/refinemenet *) 
  let _ = Kind_refine.set_num_abstract () in
  let _ = Kind_refine.set_not_fully_refined() in
  let refinement_pass = ref false in (* set to true if doing another pass after refining *)
  let newly_refined_vars = ref [] in (* all vars refined this base k *) 
  let first_time_n_values = (Array.to_list (Array.init (!k_inc-1) (fun x -> x+1))) in
  let final_position = 0 in
   
 while not !local_base_stop do 
   if iprobe step_proc any_tag comm_world = None then
     begin
       let k = !k_inc in
       let k1 = k-1 in
       let k_s = string_of_int k in 
       let _ = debug_proc BASE_PROC (Some true) ("MULTI: Checking K = "^k_s^" . No message received.") in
	 if not !refinement_pass then
	   begin
	     let _ = debug_proc BASE_PROC None "MULTI: Not refinement_pass" in
	       (* handle assertions *)	
	     let _ = 
	       if Lus_assertions.assertions_present() then
		 begin (* handle assertions *)
		   let _ = debug_proc BASE_PROC None "MULTI: Printing assertion." in
		     print_to_solver (
		       Lus_convert_yc.simple_command_string
			 (ASSERT(
			    F_PRED(solver#get#assertions,[NUM(sol.add*k1)]))));
		     if !local_firsttime then
		       for i= 0 to k1-1 do
			 print_to_solver (
			   Lus_convert_yc.simple_command_string
                             (ASSERT(
			      F_PRED(solver#get#assertions,[NUM(sol.add*i)]))));
			 debug_proc BASE_PROC None "MULTI: Done printing assertion.";
		       done
		 end
	     in	 
	     let _ = print_to_solver solver#get#push_string in
	     let impl_premise = F_EQ(POSITION_VAR(sol.nstart),NUM(sol.add*k1),L_INT) in
             let impl_result = 
	       if !local_firsttime && k > 1 then
		 begin	   
		   List.fold_right (fun p p_acc ->
				      F_AND(
					List.fold_left (fun acc x  -> 
							  F_AND(F_PRED(p,[NUM(sol.add*x)]), acc)) (F_PRED (p,[NUM(0)])) first_time_n_values, p_acc))
		     !unsolved_prop_list F_TRUE
		 end
	       else
		 List.fold_left (fun p_acc p -> 
				   F_AND(F_PRED(p,[NUM(final_position)]), p_acc)) F_TRUE !unsolved_prop_list	 
	     in
	       print_to_solver(Lus_convert_yc.simple_command_string (ASSERT(F_NOT(F_IMPL(impl_premise,impl_result)))))
	   end (* not refinement_pass *)
	 else
	   begin
	     let _ = print_to_solver solver#get#safe_push in
	     let _ = print_to_solver (Lus_convert_yc.simple_command_string (QUERY(F_TRUE))) in ()
	   end;	 
	 let _ = print_to_solver ( Lus_convert_yc.simple_command_string (QUERY(F_TRUE))) in
	 let _ = print_to_solver solver#get#done_string in
	   
	 let out_base = solver#get#get_solver_output BASE_PROC sol.from_solver_ch in
	   if (solver#get#result_is_unsat out_base) then
       begin (* base valid *)
	 let _ = debug_proc BASE_PROC (Some true) "MULTI: Valid base case." in
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
	   
	 let _ = Kind_support.persistent_step_asserts_concrete sol.def_hash sol.startdepth sol.add k sol.from_checker_ch in 
	 let _ = local_firsttime := false in
	   incr k_inc
       end (* base valid *)
     else if (solver#get#result_is_sat out_base) then
       begin (* base invalid *)
	 	let _ = debug_proc BASE_PROC (Some true) "MULTI: Invalid base case." in 
	 	let foundvars = solver#get#get_cex BASE_PROC out_base print_to_solver sol.from_solver_ch in
	 	let _ = debug_proc BASE_PROC None "MULTI: Updating list of properties" in
	 	let basestep = if !local_firsttime then BASE_INIT else BASE in
	 	let _ = 
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
				      Kind_support.persistent_step_single_assert sol.def_hash sol.startdepth sol.add basestep i y
			   	    done
			   		) xs;
		       (* note these new vars *)
		       newly_refined_vars :=  List.rev_append (!newly_refined_vars) xs;
		       refinement_pass := true
             end 
	 	in

	 (* We classify the properties in SAT and UNSAT from the value ID that we get from the counterexample *)
	   if !local_firsttime then (
	     let _ = debug_proc BASE_PROC None ("MULTI: List of properties before filtering up to the depth:") in
	       debug_prop_id BASE_PROC !sat_id_prop_list;
	
	     let sat_id_found, unsat_id_found = Multi_prop_util.filter_props !sat_id_prop_list foundvars k1 in
	       sat_id_prop_list := sat_id_found;
	       unsat_id_prop_list := unsat_id_found;
	       let _ = debug_proc BASE_PROC None ("MULTI: List of invalid properties up to the depth:") in
		 debug_prop_id BASE_PROC !sat_id_prop_list;
	   )else(
	     sat_id_prop_list := 
	       List.filter (fun id -> Multi_prop_util.is_false (Hashtbl.find foundvars (id,0))) !sat_id_prop_list;
	     unsat_id_prop_list := 
		 List.filter (fun id -> Multi_prop_util.is_true (Hashtbl.find foundvars (id,0))) !unsat_id_prop_list );
	   
	   
	   (*We update the VAR of the properties and we also update the list of unsolved properties *)
	 let _ = unsat_var_prop_list := List.map (fun x -> (Tables.get_varinfo_name x)) !unsat_id_prop_list in
	 let _ = sat_var_prop_list :=  List.map (fun x -> (Tables.get_varinfo_name x)) !sat_id_prop_list in
	 let _ = unsolved_prop_list := List.filter(fun x ->  not (List.mem x !sat_var_prop_list)) !unsolved_prop_list in
	 let _ = invalid_properties := List.append !invalid_properties (List.map (fun x -> Multi_prop_util.get_real_prop_name x) !sat_var_prop_list) in
	 let _ = invalid_var_prop := List.append !invalid_var_prop !sat_var_prop_list in
	   
	 let _ =  debug_proc BASE_PROC None ("MULTI: List of invalid properties. ID and VAR: ") in
	   debug_prop_id BASE_PROC !sat_id_prop_list; debug_prop_var BASE_PROC !sat_var_prop_list;
	 let _ = debug_proc BASE_PROC None ("MULTI: List of valid properties. ID and VAR:  ") in
	     debug_prop_id BASE_PROC !unsat_id_prop_list; debug_prop_var BASE_PROC !unsat_var_prop_list;

	 (* Check if there are invalid properties *)
	 if (List.length !sat_id_prop_list!=0) then 
	   begin
	     (* Update the real name of the properties.*)
	     let _ = debug_proc BASE_PROC None "MULTI: DONE Updating list of properties " in
	     let _ = Globals.base_time_stop := (wtime()) in
	     let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
	     let bt_string = string_of_float base_time in 
		 let prop_names =  Multi_prop_util.mk_prop_names !sat_var_prop_list in
		   print_string (Kind_support.print_resultProp_xml 
				{result=INVALID;
				 foundvars= Some foundvars;
				 minstep=Some 0;
				 maxstep=Some k1;
				 induct_cex= None;
				 name=prop_names;
				 k=k_s;
				 time=bt_string});
	     if (List.length !unsolved_prop_list == 0) then
	     	begin
	       		make_notification !valid_properties !invalid_properties;
		   		local_base_stop := true
	     	end
	   	else
	       begin
		 	let _ = debug_proc BASE_PROC (Some true) "MULTI: Sending invalid property list -> [" in
		   		List.iter(fun x -> debug_proc BASE_PROC (Some true) (x^" ")) !sat_var_prop_list;
		   		debug_proc BASE_PROC (Some true) "] to INDUCTIVE PROC.\n";
		   	let msg_to_ind_proc = M_STEP_INVALID(!sat_var_prop_list) in
		    	 isend msg_to_ind_proc step_proc 8 comm_world; 	      
		    let _ = print_to_solver solver#get#pop_string in
		    	 local_firsttime := if (k1 == (sol.startdepth-1)) then true else false;	       
	       end;
	   end
	 else
	   begin
	     debug_proc BASE_PROC None "No invalid properties to send.";
	     if (List.length !unsolved_prop_list == 0) then (
	       	make_notification !valid_properties !invalid_properties;
	       	local_base_stop := true
		  );
	   end;
	 (* Once we update the unsolved propo list, we update the sat and the unsat list*)
	 debug_proc BASE_PROC None "Updating the property ids.";
	 sat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) !unsolved_prop_list;
	 unsat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) !unsolved_prop_list;
       end (* base invalid *)
     else
       begin
         if (solver#get#result_is_error out_base) then
           print_to_user_final ((Str.matched_string out_base)^"\n");
         let _ = debug_proc BASE_PROC None ("SOLVER OUTPUT: "^out_base) in
	   Globals.base_time_stop := (wtime());
	   base_error := true;
           local_base_stop := true
       end
     end
   else

     (**********  Recieved a message ***********)
 
begin
  let _ = debug_proc BASE_PROC (Some true) "MULTI: Received a message from Inductive Step process. " in
  let list_of_valid_proc = receive step_proc any_tag comm_world in
    match list_of_valid_proc with
	M_STEP_VALID(valid_prop_ind, inv_generated, prop_as_inv, new_k) -> 
	  begin
	  	let _ = debug_proc BASE_PROC (Some true) "Current Invalid Properties: " in
		let _ = List.iter(fun x -> debug_proc BASE_PROC (Some true) (x^" ")) !invalid_var_prop in
		let _ = debug_proc BASE_PROC (Some true) "Properties from Inductive Step process: " in
		let _ = List.iter(fun x -> debug_proc BASE_PROC (Some true) (x^" ")) valid_prop_ind in
	  	let filtered_dup_properties = check_duplicates !invalid_var_prop valid_prop_ind in
	  	let _ = debug_proc BASE_PROC (Some true) "Properties to be verified: " in
			List.iter(fun x -> debug_proc BASE_PROC (Some true) (x^" ")) filtered_dup_properties;

	    if ((new_k >= !k_inc) && ((List.length filtered_dup_properties) == 0))  then 
	      begin 
			let _ = debug_proc BASE_PROC (Some true) "MULTI: Extra checks are needed." in

			(* Get rid off the property which are already discovered to be invalid *)
			let recheck_sat_list = List.filter(fun x -> not (List.mem x !invalid_var_prop)) valid_prop_ind in
		  
			(*Auxiliary check of the properties*)
			let sure_invalid, co_validated = Extra_checks.multi_bmc sol recheck_sat_list !k_inc new_k in
			let _ = debug_proc BASE_PROC None "MULTI: Validated properties after auxiliary check." in
			let _ = debug_prop_var BASE_PROC co_validated in
			let _ = debug_proc BASE_PROC None "MULTI: Invalid properties after auxiliary check." in
			let _ = debug_prop_var BASE_PROC sure_invalid in
		  		valid_properties := List.append !valid_properties (List.map (fun x -> Multi_prop_util.get_real_prop_name x) co_validated);
		  		invalid_properties := List.append !invalid_properties (List.map (fun x -> Multi_prop_util.get_real_prop_name x) sure_invalid);
		  
		  	(* Eliminate the validated and invalidate properties from the unsolved_prop_list *)
		  		unsolved_prop_list := List.filter(fun x -> not (List.mem x co_validated)) !unsolved_prop_list;
		  		unsolved_prop_list := List.filter(fun x -> not (List.mem x sure_invalid)) !unsolved_prop_list;
	      end
	    else if ((List.length filtered_dup_properties) != 0) then
	    	begin
	    		let _ = debug_proc BASE_PROC (Some true) "MULTI: Duplicate properties. Filtering." in
	    		let _ = debug_proc BASE_PROC (Some true) "MULTI: Sending properties to be rechecked -> [" in
		   			List.iter(fun x -> debug_proc BASE_PROC (Some true) (x^" ")) filtered_dup_properties;
		   			debug_proc BASE_PROC (Some true) "] to INDUCTIVE PROC.\n"; 
		   		let msg_to_ind = RECHECK(filtered_dup_properties) in
		     		send msg_to_ind step_proc 100 comm_world; () 
	    	end
	    else
	      begin
			(* Eliminate from valid_prop_ind all the properties that are invalid *)
			let filtered_prop_ind =  List.filter(fun x -> not (List.mem x !invalid_var_prop)) valid_prop_ind in
		  	(* Append all the properties that are valid *)
			let _ = valid_properties := List.append !valid_properties (List.map (fun x -> Multi_prop_util.get_real_prop_name x) filtered_prop_ind) in
			let _ = unsolved_prop_list := List.filter(fun x -> not (List.mem x filtered_prop_ind)) !unsolved_prop_list in
			let _ = Globals.base_time_stop := (wtime()) in
			let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
			let bt_string = string_of_float base_time in 
			let k_s = string_of_int new_k in 
		    let prop_names =  Multi_prop_util.mk_prop_names valid_prop_ind in
		      print_string (Kind_support.print_resultProp_xml 
				   {result=VALID;
				    foundvars=None;
				    minstep=None;
				    maxstep=None;
				    induct_cex= None;
				    name=prop_names;
				    k=k_s;
				    time=bt_string})
	      end;
	  		debug_proc BASE_PROC None "MULTI: Done verification of properties from Inductive Step process.";
	    if (List.length !unsolved_prop_list == 0) then (
			make_notification !valid_properties !invalid_properties;
		    local_base_stop := true; 
		  )
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
      Globals.base_time_stop := (wtime());
      let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
      let bt_string = string_of_float base_time in 
	  let prop_names =  Multi_prop_util.mk_prop_names !unsolved_prop_list in
	  	print_string (Kind_support.print_resultProp_xml 
		       {result=TIMEOUT;
			foundvars=None;
			minstep=None;
			maxstep=None;
			induct_cex= None;
			name=prop_names;
			k="";
			time=bt_string});
	if !Flags.mpi_abort then
	  (mpi_abort();
	  )else(
	    let _ = isend STOP step_proc 10 comm_world in
	    let _ = proc_size ==2 or ( debug_proc BASE_PROC (Some true) "Sent a STOP message to INV GEN";isend STOP 2 9 comm_world;true) in
	      local_base_stop := true));
 done; (* main loop *) 

print_string ("</Results>")






