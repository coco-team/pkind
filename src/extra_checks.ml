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

(** A module for rechecking the results of certain properties. *)

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

(** Function to do extra checks during incremental multiple generation *)

let induct_check sol unsat_prop_list inv_generated prop_as_inv k = 
  debug_proc EXTRA_PROC None "EXTRA CHECKS. Started";
  let real_unsat = ref false in
  let k1 = !k-1 in
  let k_s = string_of_int !k in
  let firststep = ref true in
  let step_error = ref false in
  let switch_to_static_compression = ref false in
  let perform_step_check = ref true in
  let initialize_step = ref true in
  let previous_static_compression = ref static_path_compression.(step_abstr) in 
  let new_unsat_list = ref [] in 
  let from_checker_ch, from_solver5_ch = Kind_support.setup_solver_induct_checker () in

   (*Creating lists*)
  let unsat_var_prop_list  = ref [] in
  let sat_var_prop_list  = ref [] in 
  let unsat_id_prop_list  = ref [] in
  let sat_id_prop_list  = ref [] in
  let prop_to_be_checked = ref [] in
    

  (* Initial list of properties*)
  unsat_var_prop_list := unsat_prop_list; 
  sat_var_prop_list := unsat_prop_list; 
  unsat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) unsat_prop_list;
  sat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) unsat_prop_list;
  prop_to_be_checked := unsat_prop_list;
  
  debug_proc EXTRA_PROC None ("EXTRA CHECKS: Performing extra checks on UNSAT props for K = "^k_s ^" on the following properties:");
  debug_prop_id EXTRA_PROC !unsat_id_prop_list;

 (* print definitions *)
  Kind_support.print_defs_to_solver_induct_checker from_solver5_ch (sol.defdoc^"\n");
 
  let all_checked = ref true in
    
 while (!all_checked) do
   if !initialize_step || not !previous_static_compression then
     begin (* setup step loop *)
       initialize_step := false;
       debug_proc EXTRA_PROC None "EXTRA CHECKS: setup step loop - Normal initialize step.";
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
	       debug_proc EXTRA_PROC None ";4";
               print_to_solver5 header_string;
             Kind_compression.abstracted_compression_constraint sol.startdepth sol.add print_to_solver5 0 (k1-sol.startdepth) sol.nvar ;
           with NoStatefulVars -> 
	     debug_proc EXTRA_PROC None ";4e";
             print_to_solver5 solver#get#push_string(***** PUSH *****) 
             | AllStatefulVarsRefined ->
                 static_path_compression.(step_abstr) <- true;
                 Kind_compression.general_compression_constraint sol.startdepth sol.add print_to_solver5 0 (k1-sol.startdepth) sol.nvar;
                 previous_static_compression := true;
		 debug_proc EXTRA_PROC None ";4f";
                 print_to_solver5 solver#get#push_string(***** PUSH *****)
         end
       else
         begin
           print_to_solver5 solver#get#push_string;(***** PUSH *****)
	   debug_proc EXTRA_PROC None ";4b";
           previous_static_compression := true
         end;
       
       
       for i=0 to (!k-1) do
         if !var_defs_mode then
	   Kind_support.def_assert_both5 sol.def_hash "DEF" [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))] !k from_checker_ch
         else
           begin
             print_to_solver5
               (Lus_convert_yc.simple_command_string
		  (ASSERT(
                     F_PRED("DEF",[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))])
                   )))
           end
       done;

       (*Assert isol.nvariants discovered if any *)
       if not (List.length inv_generated == 0) then
	 (debug_proc EXTRA_PROC None  "EXTRA CHECKS: DISCOVERED INVARIANTS";
	  List.iter (fun x -> Kind_support.print_defs_to_solver_induct_checker from_solver5_ch (x^"\n")) inv_generated;
	  for i=0 to (!k-1) do   
            print_to_solver5 (
                  Lus_convert_yc.simple_command_string
                    (ASSERT(F_PRED(solver#get#assertions_inv,[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))])))); 
	  done; 
	 );
       
       (*Assert proven properties if any *)
       if not (List.length prop_as_inv == 0) then
	 (debug_proc EXTRA_PROC None "MULTIPLE EXTRA CHECK: PROPERTY AS INVARIANTS";
	   List.iter( fun x -> print_to_solver5("(assert ("^ x ^ " (+ _n 0)))\n")) prop_as_inv;
	   for j=1 to (!k-1) do
	    List.iter( fun x -> print_to_solver5("(assert ("^ x ^ " (- _n "^string_of_int(j)^")))\n")) prop_as_inv
           done;
	 );
       
       for i=1 to (!k-1) do
	   List.iter( fun x -> print_to_solver5("(assert ("^ x ^ " (- _n "^string_of_int(i)^" )))\n")) !prop_to_be_checked
       done;
       if (List.length !prop_to_be_checked ==1) then
	 begin
	   print_to_solver5("(assert ( not ");
	   List.iter(fun x -> print_to_solver5("("^x^" _n)")) !prop_to_be_checked;
	   print_to_solver5("))"); 
	   print_to_solver5("\n"); 
	   end
       else
	 begin
	   print_to_solver5("(assert ( not ( and");
	   List.iter(fun x -> print_to_solver5("("^x^" _n)")) !prop_to_be_checked;
	   print_to_solver5(")))"); 
	   print_to_solver5("\n"); 
	 end;
     end (* setup step loop *)
 else
  begin (* alt setup step loop *)
 
    debug_proc EXTRA_PROC None "EXTRA CHECKS: setup step loop - no initialize";
   print_to_checker solver#get#push_string;
     
   for i=(!k-sol.startdepth) to (!k-1) do
     if !var_defs_mode then
       Kind_support.def_assert_both5 sol.def_hash "DEF" [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))] !k from_checker_ch
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
	     Kind_support.def_assert_both5 sol.def_hash defname [PLUS(POSITION_VAR(sol.nvar),NUM(i*sol.add))] !k from_checker_ch
           else
             begin
	       print_to_checker (Lus_convert_yc.simple_command_string
	               (ASSERT(F_PRED(defname,[PLUS(POSITION_VAR(sol.nvar),NUM(sol.add*i))]))))
             end
         done
     end
  end;
 
let assert_base = (F_EQ(POSITION_VAR(sol.nstart),NUM(sol.add*k1),L_INT)) in
print_to_solver5 (Lus_convert_yc.simple_command_string (ASSERT assert_base));
print_to_solver5 solver#get#safe_push; (* SAFE PUSH 1 *)
print_to_solver5 (Lus_convert_yc.simple_command_string(QUERY(F_TRUE)));
print_to_solver5 solver#get#done_string;


let out_step_extra = solver#get#get_solver_output EXTRA_PROC from_solver5_ch in
  if (solver#get#result_is_unsat out_step_extra) then
    begin (* step valid *)  
      print_to_solver5 solver#get#safe_pop; (* SAFE PUSH 1 *)
      if !check_compression && !loopfree_mode && not static_path_compression.(step_abstr) then
          begin
            debug_proc EXTRA_PROC None("EXTRA CHECKS: Re-checking with full compression.\n");
            switch_to_static_compression := true;
            print_to_solver5 solver#get#pop_string;
            (* sol.add the static def here *)
            initialize_step := true;
            perform_step_check := true 
          end
       else 
        begin
	  debug_proc EXTRA_PROC None("\nEXTRA CHECKS: All properties are valid -> [");
	  List.iter(fun x -> debug_proc EXTRA_PROC None(x^" ")) !prop_to_be_checked;
	  debug_proc EXTRA_PROC None("].\n");
	  all_checked := false;
	  real_unsat :=true;
	  new_unsat_list := !prop_to_be_checked;
        end 
    end (* step valid *)

else if (solver#get#result_is_sat out_step_extra || solver#get#result_is_unknown out_step_extra) then
begin (* step invalid *)
  if solver#get#result_is_unknown out_step_extra then
    debug_proc EXTRA_PROC None ("EXTRA CHECKS: Unknown in "^k_s^" steps.\n")
  else
    debug_proc EXTRA_PROC None ("EXTRA CHECKS: step is Invalid at K = "^k_s^".\n");
   let foundvars = solver#get#get_cex EXTRA_PROC out_step_extra print_to_solver5 from_solver5_ch in
   let simulation_value_hash = solver#get#get_simulation_cex EXTRA_PROC out_step_extra print_to_solver5 from_solver5_ch  in
   let value_n = (Hashtbl.find simulation_value_hash ("_n")) in
   
    debug_proc EXTRA_PROC None ("EXTRA CHECKS: Updating list of properties.\n");
     
    unsat_id_prop_list := 
      List.filter (fun id -> Multi_prop_util.is_false 
		     (Hashtbl.find foundvars (id,int_of_string(value_n)))) !unsat_id_prop_list;

     sat_id_prop_list := 
      List.filter (fun id -> Multi_prop_util.is_true 
		     (Hashtbl.find foundvars (id,int_of_string(value_n)))) !sat_id_prop_list;
   
    unsat_var_prop_list := List.map (fun x -> (Tables.get_varinfo_name x)) !unsat_id_prop_list;
    
    sat_var_prop_list :=  List.map (fun x -> (Tables.get_varinfo_name x)) !sat_id_prop_list;
     
    debug_proc EXTRA_PROC None("EXTRA CHECKS: SAT Properties at K = "^k_s^""); 
    debug_prop_var EXTRA_PROC !unsat_var_prop_list;
    debug_proc EXTRA_PROC None("EXTRA CHECKS: UNSAT Properties at K = "^k_s^" "); 
    debug_prop_var EXTRA_PROC !sat_var_prop_list;
    prop_to_be_checked := !sat_var_prop_list;
    if (List.length !prop_to_be_checked == 0) then
    ( debug_proc EXTRA_PROC None("EXTRA CHECKS: All SAT. Return to STEP PROC.");
      all_checked := false;
    ) else (
     print_to_solver5 solver#get#pop_string;
     initialize_step := true;
     debug_proc EXTRA_PROC None ("EXTRA CHECKS: Done Updating list of properties.");
     real_unsat := false;
    );
end (* step invalid *)
  else
    begin
      (* STEP check = ERROR *)
      debug_proc EXTRA_PROC None ("EXTRA CHECKS: Abort in "^k_s^" steps.\n");
      if (solver#get#result_is_error out_step_extra) then
	print_to_user_final ((Str.matched_string out_step_extra)^"\n");
      debug_proc EXTRA_PROC None ("EXTRA CHECKS : "^out_step_extra);
      step_error := true
    end;
  
    (*Resetting the current logical context *)
    done;
    print_to_solver5("(reset)");
    !real_unsat,
  !new_unsat_list
    
 

(** Extra checks done in the base case process, i.e., when the received k is greater than the current k *)

let multi_bmc sol prop_tbc current_k new_k = 
  let _ = debug_proc BASE_PROC None ("MULTI: Extra checks of the following props from current K = " ^ string_of_int(current_k) ^ " to a new K = "^ string_of_int(new_k) ^ ":") in
  let _ = debug_prop_var BASE_PROC prop_tbc in
    
  (* List of properties *)
  let unsolved_prop_list = ref [] in
  let unsat_id_prop_list  = ref [] in
  let sat_id_prop_list  = ref [] in
  let unsat_var_prop_list  = ref [] in
  let sat_var_prop_list  = ref [] in 

    
  (* Initial list of properties*)
  let _ = unsolved_prop_list := prop_tbc in
  let _ = unsat_var_prop_list := prop_tbc in 
  let _ = sat_var_prop_list := prop_tbc in
  let _ = unsat_id_prop_list :=  List.map (fun x -> Tables.varid_lookup x) prop_tbc in
  let _ = sat_id_prop_list :=  List.map (fun x -> Tables.varid_lookup x) prop_tbc in
  let k = ref (current_k-1) in

    
  (* Print definition to solver 4*)
  let from_checker_ch, from_solver4_ch = Kind_support.setup_solver_bmc_checker () in
  let _ = Kind_support.print_defs_to_solver_bmc_checker from_solver4_ch (sol.defdoc^"\n") in
    
  (* Assert the TS from the 0 to the current k *)
    for i=0 to !k do 
      Kind_support.persistent_assert_bmc sol.def_hash sol.startdepth sol.add i sol.from_checker_ch;
    done;

    (*Assert the property from 0 to current k-1 *)
     for i=0 to (!k-1) do 
      List.iter(fun x -> print_to_solver4("(assert ("^x^" (- 0 "^string_of_int(i)^")))\n")) !unsolved_prop_list;
     done; 

 (* Loop between the current k and the new k*)
  while (!k < new_k) do	
    let _ = 
      if Lus_assertions.assertions_present() then
	( (* handle assertions *)
	  let _ = debug_proc BASE_PROC None "MULTIPLE EXTRA CHECK: Printing assertion." in
	    for i=0 to !k do
	      print_to_solver4 (
		Lus_convert_yc.simple_command_string
                  (ASSERT(
		     F_PRED(solver#get#assertions,[NUM(sol.add*i)]))));
	      debug_proc BASE_PROC None "MULTIPLE EXTRA CHECK: Done printing assertion.";
	    done
	)
    in
      (* Assert the property at k*)
    let _ = print_to_solver4 solver#get#push_string in
    let _ = print_to_solver4("(assert (not ( => (= _base (- 0 "^string_of_int(!k-1)^"))") in
      if (List.length !unsolved_prop_list == 1) then
	(
	  List.iter(fun x -> print_to_solver4("("^x^" ")) !unsolved_prop_list;
	  print_to_solver4("(- 0 "^string_of_int(!k)^")))))\n");
	) else (
	  print_to_solver4("(and ");
	  List.iter(fun x -> print_to_solver4("("^x^"(- 0 "^string_of_int(!k)^")))")) !unsolved_prop_list;
	  print_to_solver4("))))\n");
	);

      let _ = print_to_solver4 (Lus_convert_yc.simple_command_string (QUERY(F_TRUE))) in
      let _ = print_to_solver4 solver#get#done_string in
      let out_base = solver#get#get_solver_output BASE_PROC from_solver4_ch in
	if (solver#get#result_is_unsat out_base) then
	  begin (* base valid *)
	    let _ = debug_proc BASE_PROC None "MULTIPLE EXTRA CHECK: Valid." in
	    let _ = print_to_solver4 solver#get#pop_string in
	      (* if we have analyzed all the properties then exit, otherwise increase k *)
	      if (List.length !unsolved_prop_list !=0) then (
		for i=0 to !k do
		  List.iter(fun x -> print_to_solver4("(assert ("^x^" (- 0 "^string_of_int(i)^")))\n")) !unsolved_prop_list;
		done;
		Kind_support.persistent_step_asserts_concrete sol.def_hash sol.startdepth sol.add !k sol.from_checker_ch;  
		k := !k + 1);
        (*!sat_var_prop_list must be set to empty, because we have validated all props*)
        sat_var_prop_list := []; 
	      !sat_var_prop_list, !unsat_var_prop_list;
 end (* base valid *)
	else if (solver#get#result_is_sat out_base) then
	  begin (* base invalid *)
	    let _ = debug_proc BASE_PROC None "MULTI: Invalid base case." in 
	    let _ = print_to_solver4 solver#get#pop_string in
	    let foundvars = solver#get#get_cex BASE_PROC out_base print_to_solver4 from_solver4_ch in     
	    let _ = debug_proc BASE_PROC None "MULTI: Filter the different properties. SAT and UNSAT list before: " in
	    let _ = debug_prop_id BASE_PROC !sat_id_prop_list in
	    let _ = debug_prop_id BASE_PROC !unsat_id_prop_list in 
	    let _ = 
	      sat_id_prop_list := 
		List.filter (fun id -> Multi_prop_util.is_false 
			       (Hashtbl.find foundvars (id,(-(!k))))) !sat_id_prop_list in
	    let _ = 
	      unsat_id_prop_list := 
		List.filter (fun id -> Multi_prop_util.is_true 
			       (Hashtbl.find foundvars (id,(-(!k))))) !unsat_id_prop_list in 
	    let _ = debug_proc BASE_PROC None "MULTI: SAT and UNSAT list after: " in
	    let _ = debug_prop_id BASE_PROC !sat_id_prop_list in
	    let _ = debug_prop_id BASE_PROC !unsat_id_prop_list in
	    let _ = unsat_var_prop_list := List.map (fun x -> (Tables.get_varinfo_name x)) !unsat_id_prop_list in
	    let _ = sat_var_prop_list :=  List.map (fun x -> (Tables.get_varinfo_name x)) !sat_id_prop_list in
	    let _ = debug_proc BASE_PROC None "MULTI: Unsolved properties list before: " in
	    let _ = debug_prop_var BASE_PROC !unsolved_prop_list in
	    let _ = unsolved_prop_list := List.filter(fun x ->  not (List.mem x !sat_var_prop_list)) !unsolved_prop_list in
	    let _ = unsolved_prop_list := List.filter(fun x ->  not (List.mem x !unsat_var_prop_list)) !unsolved_prop_list in
	    let _ = debug_proc BASE_PROC None "MULTI: Unsolved properties list after: " in
	    let _ = debug_prop_var BASE_PROC !unsolved_prop_list in
	    let _ = Globals.base_time_stop := (wtime()) in
	    let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
	    let bt_string = string_of_float base_time in 
	      if !Flags.xml then (
		let prop_names =  Multi_prop_util.mk_prop_names !sat_var_prop_list in
		  print_xml (Kind_support.print_resultProp_xml 
			       {result=INVALID;
				foundvars= Some foundvars;
				minstep=Some 0;
				maxstep=Some !k;
				induct_cex= None;
				name=prop_names;
				k=(string_of_int !k);
				time=bt_string});
	      ) else (
		print_to_user_final("\n\n++++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
		print_to_user_final("PROPERTY [");
		List.iter (fun x -> print_to_user_final(Multi_prop_util.get_real_prop_name (x)^" ")) !sat_var_prop_list;
		print_to_user_final ("] is Invalid. ||  K = "^(string_of_int !k)^ " || Time = "^bt_string^" || COUNTEREXAMPLE:\n");
		Kind_support.print_countermodel foundvars 0 !k; 
		print_to_user_final("++++++++++++++++++++++++++++++++++++++++++++++++++++++\n\n"););
	      k := !k + 1;
	      !sat_var_prop_list, !unsat_var_prop_list
	  end (* base invalid *)
	else
	  begin
            if (solver#get#result_is_error out_base) then
              print_to_user_final ((Str.matched_string out_base)^"\n");
            let _ = debug_proc BASE_PROC None ("SOLVER OUTPUT: "^out_base) in
	      exit 0
	  end 
  done;
  !sat_var_prop_list, !unsat_var_prop_list ;;


(** Extra checks done in the base case process in the case of single property, i.e., when the received k is greater than the current k *)

let single_bmc new_k current_k sol = 
 
  (* For Abstraction/refinemenet *) 
  let _ = Kind_refine.set_num_abstract () in
  let _ = Kind_refine.set_not_fully_refined() in
  let refinement_pass = ref false in (* set to true if doing another pass after refining *)
  let newly_refined_vars = ref [] in (* all vars refined this base k *)  
  let k = ref current_k in
  let result = ref true in
    
 while (!k == new_k) do
   let k1 = !k-1 in
   let k_s = string_of_int !k in
   let _ = debug_proc BASE_PROC None ("Extra checks at K = "^k_s) in
     if not !refinement_pass then
       begin (* not refinement_pass *)
	 let _ = debug_proc BASE_PROC None "no refinement_pass" in	 
	 let _ =
	   if Lus_assertions.assertions_present() then
	     (
	       let _ = debug_proc BASE_PROC None "Has assertions." in
		 print_to_solver (
		   Lus_convert_yc.simple_command_string
		     (ASSERT(
			 F_PRED(solver#get#assertions,[NUM(sol.add*(!k))]))))
	      );
	   debug_proc BASE_PROC None "Has assertions. Done. ";
	 in
	 let _ = print_to_solver solver#get#push_string in
	   
         (* Assert the properties here*)
         let impl_premise = F_EQ(POSITION_VAR(sol.nstart),NUM(sol.add*k1),L_INT) in
         let impl_result =  F_PRED("P",[NUM(0)]) in
         let _ = print_to_solver(Lus_convert_yc.simple_command_string (
				   ASSERT(
				     F_NOT(F_IMPL(impl_premise,impl_result))))) in
         let _ = print_to_solver solver#get#safe_push (* PUSH 2a *)  in
           print_to_solver ( Lus_convert_yc.simple_command_string (QUERY(F_TRUE)))
       end (* not refinement_pass *)
     else
       begin
         let _ = print_to_solver solver#get#safe_push in
           print_to_solver (Lus_convert_yc.simple_command_string (QUERY(F_TRUE)))
       end;
     let _ = print_to_solver solver#get#done_string in
       
     let out_base = solver#get#get_solver_output BASE_PROC sol.from_solver_ch in
       if (solver#get#result_is_unsat out_base) then
	 begin (* base valid *)
	   let _ = print_to_solver solver#get#safe_pop in
	   let _ = debug_proc BASE_PROC None "Valid" in
	   let _ = print_to_solver solver#get#pop_string in
	     (* re-assert the base defs for all newly refined vars *)
	   let _ = 
		  List.iter (fun y ->
			       Kind_support.print_initialization_single sol.def_hash sol.startdepth sol.add y;
			       for i=sol.startdepth to !k-1 do
				 Kind_support.persistent_step_single_assert sol.def_hash sol.startdepth 
				   sol.add BASE i y
			       done
			    ) !newly_refined_vars in
	   let  _ = print_to_solver  (Lus_convert_yc.simple_command_string (ASSERT( F_PRED("P",[NUM(sol.add*(!k))])	)))  in
	     (*Incrementing K*)
	     if (!k < new_k) then 
	        (Kind_support.persistent_step_asserts_concrete sol.def_hash sol.startdepth sol.add !k sol.from_checker_ch);
	     let _ = refinement_pass := false in
	       k:=!k+1;
	 end (* base valid *)	  
       else if (solver#get#result_is_sat out_base) then
	 begin (* base invalid *)
	   let _ = debug_proc BASE_PROC None "Invalid." in
	   let basestep = BASE in
	   let foundvars = solver#get#get_cex BASE_PROC out_base print_to_solver sol.from_solver_ch in
	   let _ = debug_proc BASE_PROC None ("checking absmode "^(string_of_int (Kind_refine.get_num_abstract base_abstr))) in
	   let _ = print_to_solver solver#get#safe_pop in
	     if !abs_mode && Kind_refine.is_not_fully_refined base_abstr then
	       begin
		 match Kind_refine.check_and_refine_abstraction sol.from_checker_ch 
		   sol.def_hash sol.startdepth sol.add basestep foundvars sol.pvars !k with
		       CHECK_IS_VALID -> () (* continue *)
		     | CHECK_IS_INVALID xs ->
			 (* assert new vars *)
			 List.iter (fun y ->
				      (* assert just y up to base step *)
				      Kind_support.print_initialization_single sol.def_hash 
					sol.startdepth sol.add y;
				      (* assert just y from sol.startdepth to k-1 *)
				      for i=sol.startdepth to !k-1 do
					Kind_support.persistent_step_single_assert sol.def_hash 
					  sol.startdepth sol.add basestep i y
				      done
				   ) xs;
			 (* note these new vars *)
			 newly_refined_vars :=  List.rev_append (!newly_refined_vars) xs;
			 refinement_pass := true
	       end
	     else
	       begin	       
		 let _ = debug_proc BASE_PROC None ("Invalid at K = "^k_s^".\n") in   
		 let _ = Globals.base_time_stop := (wtime()) in
		 let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
		 let bt_string = string_of_float base_time in 
		   if !Flags.xml then (
		     print_xml (Kind_support.print_resultProp_xml 
				  {result=INVALID;
				   foundvars= Some foundvars;
				   minstep=Some 0;
				   maxstep=Some k1;
				   induct_cex= None;
				   name="Specified Property";
				   k=k_s;
				   time=bt_string});
		   ) else (
		     let _ =  print_to_user_final("FOUND COUNTEREXAMPLE at K = "^k_s^"\n\n") in
		     let _ = Kind_support.print_countermodel foundvars 0 k1 in
    	      	       print_to_user_final("\n\n+++   WALL TIME (ms) :- "^bt_string^"   +++\n\n");
		   );
		   if !Flags.mpi_abort then (
		     mpi_abort();
		   ) else (  
		     let _ = isend STOP step_proc 8 comm_world in
		     let _ = proc_size ==2 or (isend STOP 2 9 comm_world;true) in
		       result := false;
		       exit 0)
	       end
	 end (* base invalid *)
       else
	 begin
	   print_to_user_final ("Abort in "^k_s^" base due to incompleteness or error.\n");
	   if (solver#get#result_is_error out_base) then
	     print_to_user_final ((Str.matched_string out_base)^"\n");
	   let _ = debug_proc BASE_PROC None ("SOLVER OUTPUT: "^out_base) in
	     Globals.base_time_stop := (wtime());
	     exit 0;	
	 end;
 done;
    !result
    
