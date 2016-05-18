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


  
(** Extra checks done in the base case process, i.e., when the recivied k is greater than the current k *)

let multi_bmc sol prop_tbc new_k = 
  let _ = debug_proc BASE_PROC None ("MULTI: Extra checks of the following props from current K =  " ^ string_of_int(sol.startdepth) ^ " to a new K= "^ string_of_int(new_k) ^ ":") in
  let _ = debug_prop_var BASE_PROC prop_tbc in
    
  (* List of properties *)
  let unsolved_prop_list = ref [] in
  let unsat_id_prop_list  = ref [] in
  let sat_id_prop_list  = ref [] in
  let unsat_var_prop_list  = ref [] in
  let sat_var_prop_list  = ref [] in 

  (* Check until stop *)
  let extra_check_stop = ref false in
    
  (* Initial list of properties*)
  let _ = unsolved_prop_list := prop_tbc in
  let _ = unsat_var_prop_list := prop_tbc in 
  let _ = sat_var_prop_list := prop_tbc in
  let _ = unsat_id_prop_list :=  List.map (fun x -> Tables.varid_lookup x) prop_tbc in
  let _ = sat_id_prop_list :=  List.map (fun x -> Tables.varid_lookup x) prop_tbc in
  let k = ref (sol.startdepth) in

    
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
  while (not !extra_check_stop) do	
    let _ = 
      if Lus_assertions.assertions_present() then
	( (* handle assertions *)
	  let _ = debug_proc BASE_PROC None "MULTI EXTRA CHECK: Printing assertion." in
	    for i=0 to !k do
	      print_to_solver4 (
		Lus_convert_yc.simple_command_string
                  (ASSERT(
		     F_PRED(solver#get#assertions,[NUM(sol.add*i)]))));
	      debug_proc BASE_PROC None "MULTI EXTRA CHECK: Done printing assertion ";
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
	    let _ = debug_proc BASE_PROC None "MULTI EXTRA CHECK: Valid" in
	    let _ = print_to_solver4 solver#get#pop_string in
	      (* if we have analyzed all the properties then exit, otherwise increase k *)
	      if (List.length !unsolved_prop_list !=0) then (
		for i=0 to !k do
		  List.iter(fun x -> print_to_solver4("(assert ("^x^" (- 0 "^string_of_int(i)^")))\n")) !unsolved_prop_list;
		done;
		Kind_support.persistent_step_asserts_concrete sol.def_hash sol.startdepth sol.add !k sol.from_checker_ch;  
		k := !k + 1);
 end (* base valid *)
	else if (solver#get#result_is_sat out_base) then
	  begin (* base invalid *)
	    let _ = debug_proc BASE_PROC None "MULTI: Invalid base case" in 
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
		let prop_names =  Multi_prop_util.mk_prop_names !sat_var_prop_list in
		  print_string (Kind_support.print_resultProp_xml 
			       {result=INVALID;
				foundvars= Some foundvars;
				minstep=Some 0;
				maxstep=Some !k;
				induct_cex= None;
				name=prop_names;
				k=(string_of_int !k);
				time=bt_string});
    if (List.length !unsolved_prop_list == 0) then
     	extra_check_stop := true;)
     else( k := !k + 1;)
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


