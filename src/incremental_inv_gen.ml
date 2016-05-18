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



(** Incremental online invariant generator *)

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


exception INV_BASE
let solver = Globals.my_solver
let toss x = () (* toss outputs *)

(** Print the invariant using the internal format of KIND *)
let print_invariant b_eqs b_imps i_eqs i_imps depth=
  let buf = Buffer.create 100 in
     Buffer.add_string buf "(define ASSERTIONS-INV :: (-> _nat bool) (lambda ( _M::nat) (ite (= _M _base) true " ;
     Buffer.add_string buf "( and";
     List.map(fun x ->   Buffer.add_string buf (Imp_graph.equ_invariant x)) b_eqs;
     List.map(fun x ->   Buffer.add_string buf (Imp_graph.imp_invariant x)) b_imps;
     List.map(fun x ->   Buffer.add_string buf (Imp_graph.int_eq_invariant x)) i_eqs;
     List.map(fun x ->   Buffer.add_string buf (Imp_graph.int_imp_invariant x)) i_imps; 
     Buffer.add_string buf "))))";
     (Buffer.contents buf);;  

let print_invariant_no_imp b_eqs b_imps i_eqs i_imps depth=
  let buf = Buffer.create 100 in
     Buffer.add_string buf "(define ASSERTIONS-INV :: (-> _nat bool) (lambda ( _M::nat) (ite (= _M _base) true " ;
    Buffer.add_string buf "( and";
    List.map(fun x ->   Buffer.add_string buf (Imp_graph.equ_invariant x)) b_eqs;
    List.map(fun x ->   Buffer.add_string buf (Imp_graph.int_eq_invariant x)) i_eqs;
    List.map(fun x ->   Buffer.add_string buf (Imp_graph.int_imp_invariant x)) i_imps; 
     Buffer.add_string buf "))))";
     (Buffer.contents buf);;  

(** Function that prints the conjunction of the discovered invariants *)
let pr_func b_eqs b_imps i_eqs i_imps depth =
  pr "-- "; 
  print_int ((List.length b_imps) 
	      + 2*(List.length b_eqs) 
	      + 2*(List.length i_eqs) 
	      + (List.length i_imps) ) ;
  pr " implications. \n";
  pr "assert";
  let pos_l = Util.n_to_m 1 depth in
    List.iter (fun x-> pr " (true -> (") pos_l ; 
    List.map(fun x -> pr (Imp_graph.eq_org x); pr " \nand ";) b_eqs;
    List.map(fun x -> pr (Imp_graph.imp_org x); pr " \nand ";) b_imps;
    List.map(fun x -> pr (Imp_graph.int_eq_org x); pr " \nand ";) i_eqs;
    List.map(fun x -> pr (Imp_graph.int_imp_org x); pr " \nand ";) i_imps;
    pr " true ";
    List.iter (fun x-> pr "))") pos_l ; 
    pr ";\n";; 



(** Main function for the incremenal invariant generation *)
let produce_invariants defdoc maxdepth def_hash pvars=  
  let _ = debug_proc INV_GEN_PROC (Some true) "Started." in

   
  debug_proc INV_GEN_PROC None ("BOOL INV: " ^ string_of_bool !Flags.invariant_bool);
  debug_proc INV_GEN_PROC None ("INT INV: " ^ string_of_bool !Flags.invariant_int);
  debug_proc INV_GEN_PROC None ("MODE INV: " ^ string_of_bool !Flags.mode_inv);
  debug_proc INV_GEN_PROC None ("ANY INTRVALS: " ^ string_of_bool !Globals.is_inter);

  (* Check that at least one flag is activated.*) 
  if ((not !Flags.invariant_bool) && (not !Flags.invariant_int) && (not !Flags.mode_inv)) then exit 0; 
  (* If Mode Inv is activated and no mode variable in the system.*) 
  if (!Flags.mode_inv && (not !Globals.is_inter)) then Flags.mode_inv := false;


  let start_time = ref 0.0 in
  let _ = start_time := (wtime()) in

  (* Generate terms and sub-terms for invariant candidates *)
  let all_terms = Lus_convert_yc.get_all_def_terms () in
  let bool_sub_exprs, int_sub_exprs, float_sub_exprs = Sub_exprs.sub_exprs all_terms Expr_util.filter_sub_exprs in
    
  (* Generate new variables for invariant candidates *)
  let nvar = solver#get#k_position_string in
  let add = Kind_support.get_add() in
  let nstart = solver#get#step_base_string in
  let startdepth = maxdepth + 1 in
  let from_checker_ch, from_solver3_ch = Kind_support.setup_solver3() in
  let _ = debug_proc INV_GEN_PROC None " Printing Lustre Program terms." in 
  let _ = Kind_support.print_defs_to_solver3 from_solver3_ch from_checker_ch (defdoc^"\n") in
  let _ = debug_proc INV_GEN_PROC None " Printing new terms." in
  let _ = print_to_solver3 solver#get#push_string in
  let _ = 
    if (!Flags.invariant_bool) then(
      let new_bool_var_doc = New_vars.bool_newvar_defs bool_sub_exprs in
	Kind_support.print_defs_to_solver3 from_solver3_ch from_checker_ch (new_bool_var_doc^"\n")) in
  let _ = 
    if (!Flags.invariant_int) then (
      let new_int_var_doc =  New_vars.int_newvar_defs int_sub_exprs in
	 Kind_support.print_defs_to_solver3 from_solver3_ch from_checker_ch (new_int_var_doc^"\n")) in 
  let _ =
    if (!Globals.is_inter && !Flags.mode_inv) then (
      List.iter (fun (v,lb,ub) -> 
		   let p, n = New_vars.mk_one_mode_candidate v lb ub in
		     Kind_support.print_defs_to_solver3 from_solver3_ch from_checker_ch (p^n)
		)(New_vars.get_interval_vars())) in
  
(* Creating bool and int equivalence classes. *)
  let bool_imp_graph =  new Imp_graph.bool_imp_graph (
      if (!Flags.invariant_bool or !Flags.mode_inv) 

        then (New_vars.get_bool_nvrs ())
      else []
    )
  in
  let ints_partial_order = new Partial_order.partial_order (
      if (!Flags.invariant_int) 
      then New_vars.get_int_nvrs ()
      else []
    ) 
  in 

  let _ = debug_proc INV_GEN_PROC None " Printing Initialization." in 
  let _ = print_to_solver3 solver#get#push_string (***** PUSH  Init of real terms*****) in
  let _ = Kind_support.print_init 3 def_hash startdepth add from_checker_ch in

  (* print new variables assertions. *)
  let _ = print_to_solver3 solver#get#push_string (***** PUSH Init of new vars*****) in
  let _ = print_to_solver3 (New_vars.mk_nvr_eq_cmds (NUM 0)) in
  let k_provided = !Flags.k_incremental in
  let first_time_round = ref true in
  let error_inv = ref false in
  let stop_inv = ref false in
  let cur_depth = ref maxdepth  in
  let refinement_base = ref 0 in 
  let base_inv_stop = ref false in
  let outer_loop_stop = ref true in
  let send_to_induct = ref true in (* Send the invariant to the induct proc *)
  let _ = Kind_support.set_last_level_asserted (startdepth-1) in


 while ((not (!cur_depth = k_provided)) && !outer_loop_stop) do
   let _ = debug_proc INV_GEN_PROC None ("INV GEN - OUTER LOOP") in
     while (not !base_inv_stop)  do
       if  iprobe base_proc any_tag comm_world = None then
	 begin
	   let _ = debug_proc INV_GEN_PROC (Some true) "BASE LOOP: No message received" in
	   let base_num = !cur_depth * add in
	   let cur_depth_s = string_of_int !cur_depth in
	   let refinement_base_s = string_of_int !refinement_base in 
	   let _ = debug_proc INV_GEN_PROC None (" ASSERTING BASE CASE AT K = "^cur_depth_s^" -- Refinement round = "^refinement_base_s^"\n") in
	   let _ = print_to_solver3 solver#get#push_string in
	   let bool_imp_doc = 
	     if (!Flags.invariant_bool || !Flags.mode_inv) then  bool_imp_graph#doc_of_asserts()
	     else []
	   in
	   let int_imp_doc =  
	     if (!Flags.invariant_int) then ints_partial_order#doc_of_asserts()
	     else []
	   in
	   let equiv_imp_doc = Expr_util.mk_not_ands (bool_imp_doc@int_imp_doc) in 
	   let _ = print_to_solver3 equiv_imp_doc in
	   let assert_base = (F_EQ(POSITION_VAR(nstart),NUM(base_num),L_INT)) in
	   let _ = print_to_solver3(Lus_convert_yc.simple_command_string (ASSERT assert_base)) in 
	   let _ = print_to_solver3(Lus_convert_yc.simple_command_string (QUERY(F_TRUE))) in
	   let _ = print_to_solver3 solver#get#done_string in
	   let _ = debug_proc INV_GEN_PROC None (" BASE - Checking entailment.\n") in
      
	   let out_base = solver#get#get_solver_output INV_GEN_PROC from_solver3_ch in
	     if (solver#get#result_is_unsat out_base) then
	       begin (* base valid *)
		 debug_proc INV_GEN_PROC None (" BASE CASE VALID AT K = "^cur_depth_s^"\n ");
		 print_to_solver3 solver#get#pop_string; (* PUSH 2 *)	    
		 base_inv_stop := true;    
	       end (* base valid *)
	     else if (solver#get#result_is_sat out_base) then
	       begin (* base invalid *)
     		 debug_proc INV_GEN_PROC None (" BASE CASE INVALID AT K = "^cur_depth_s^"\n ");      
		 let simulation_value_hash_base = 
		   solver#get#get_simulation_cex INV_GEN_PROC out_base print_to_solver3 from_solver3_ch  in
		 let changed_base  = 
		   if (!Flags.invariant_int && (!Flags.invariant_bool || !Flags.mode_inv))
		   then (
		     let ra_base = bool_imp_graph#set_new_graph simulation_value_hash_base in
		     let rb_base = ints_partial_order#sort simulation_value_hash_base in
		       if (ra_base || rb_base ) then true else false )
		   else if (!Flags.invariant_bool || !Flags.mode_inv)
		   then (bool_imp_graph#set_new_graph simulation_value_hash_base)
		   else if (!Flags.invariant_int)
		   then (ints_partial_order#sort simulation_value_hash_base)
		   else failwith "Error"
		 in
		   print_to_solver3 solver#get#pop_string;
		   print_to_solver3 solver#get#safe_pop; (* PUSH 2 *) 
		   begin
		     stop_inv := not changed_base ; 
		     if(!stop_inv ) 
		     then (
		       pr (Expr_util.mk_not_ands (bool_imp_graph#doc_of_asserts() ));
		       pr "No changes while sat.\n";
		       failwith "global stop"; )
		   end;
		   refinement_base := !refinement_base + 1;		    
	       end (* base invalid *)
	     else
	       begin
		 (* BASE check = ERROR *)
		 if (solver#get#result_is_error out_base) then
		   print_to_user_final ((Str.matched_string out_base)^"\n");
		 debug_proc INV_GEN_PROC None  ("SOLVER OUTPUT: "^out_base);
		 exit 0;
	       end;
	 end
       else
	 begin
	   debug_proc INV_GEN_PROC None ("BASE LOOP : Message received");
	   Globals.inv_gen_time_stop := (wtime());
	   exit 0;
	 end;
     done;
     
   let step_inv_stop = ref false in
   let refinement_step = ref 0 in
   let _ = print_to_solver3 solver#get#pop_string; (* POP Init of new vars from base *) in
   let _ = print_to_solver3 solver#get#pop_string; (* POP Init of real vars from base*) in
   let _ = print_to_solver3 solver#get#push_string;  (* PUSH candidate for the step case *) in
   let positions = 
     if !cur_depth ==0 then (
       debug_proc INV_GEN_PROC None ("Current depth = 0");
       List.map 
	 (fun x -> MINUS(POSITION_VAR(nvar),NUM(x))) 
	 (Util.n_to_m 0 (!cur_depth))
     )else(
       List.map 
	 (fun x -> MINUS(POSITION_VAR(nvar),NUM(x))) 
	 (Util.n_to_m 1 (!cur_depth)) 
     ) in		 
   let _ = 
     List.iter (fun x -> 
		  Kind_support.def_assert_both3 def_hash "DEF" 
		    [PLUS(POSITION_VAR(nvar),NUM(x*add))]
		    !cur_depth from_checker_ch;) (Util.n_to_m 0 (!cur_depth)) in
   let _ =print_to_solver3 (New_vars.mk_nvr_eq_cmds (POSITION_VAR(nvar))) in
     
     while (not !step_inv_stop) do
       if iprobe base_proc any_tag comm_world = None then
	 begin
	   let _ = debug_proc INV_GEN_PROC None "INDUCTIVE LOOP: No message received" in
	   let cur_depth_s = string_of_int !cur_depth in
	   let refinement_step_s = string_of_int !refinement_step in 
	   let _ = debug_proc INV_GEN_PROC None (" ASSERTING STEP CASE AT K = "^cur_depth_s^" -- Refinement round = "^refinement_step_s^"\n") in		   
	   let _ = print_to_solver3 solver#get#push_string  (* PUSH candidate for the step case *)   in
	   if (!Flags.invariant_bool || !Flags.mode_inv)
	     then (List.iter (fun x-> print_to_solver3 x;))
		 (bool_imp_graph#doc_of_stepn_asserts positions); 
	     
	   if (!Flags.invariant_int)
	      then  List.iter (fun x-> print_to_solver3 x; )
		(ints_partial_order#doc_of_stepn_asserts positions); 
	
	let bool_imp_doc = 
	  if (!Flags.invariant_bool || !Flags.mode_inv) then (bool_imp_graph#doc_of_asserts ())
	  else [] in
	let int_imp_doc = 
	  if !Flags.invariant_int then (ints_partial_order#doc_of_asserts ())
	  else [] in
	let imp_equiv_doc = Expr_util.mk_not_ands (bool_imp_doc@int_imp_doc) in   
	let _ = print_to_solver3 imp_equiv_doc in
	let _ = print_to_solver3(Lus_convert_yc.simple_command_string (QUERY(F_TRUE))) in
	let _ = print_to_solver3 solver#get#done_string in
	  
	let out_step = solver#get#get_solver_output INV_GEN_PROC from_solver3_ch in
	  if (solver#get#result_is_unsat out_step) 
	  then(
	    debug_proc INV_GEN_PROC None (" STEP CASE VALID K = "^cur_depth_s^"\n");
	    print_to_solver3 solver#get#pop_string;  (* POP Init of new vars for the step case + candidate*)
	    let b_eqs,b_imps =
	      if (!Flags.invariant_bool || !Flags.mode_inv)
	         then bool_imp_graph#eq_imp_graph()
	      else [],[] in
	    let int_eqs,int_imps =
		   if (!Flags.invariant_int)
		      then ints_partial_order#eq_imp()
		   else [],[] in
		Globals.inv_gen_time_stop := (wtime());
		debug_proc INV_GEN_PROC (Some true) (" Sending Invariant to indutive step process. \n");
		if !send_to_induct then (
		  let invariant = 
		    if !Flags.no_imp then 
		      print_invariant_no_imp b_eqs b_imps int_eqs int_imps maxdepth
	            else
		       print_invariant b_eqs b_imps int_eqs int_imps maxdepth in  
		  let s_invariant = INV_FULL(invariant) in 
		    send s_invariant step_proc 89 comm_world); 
		step_inv_stop:=true
	  ) else if (solver#get#result_is_sat out_step) 
	  then(
	    debug_proc INV_GEN_PROC None ("STEP CASE INVALID K = "^cur_depth_s^"\n");
	    let simulation_value_hash = solver#get#get_simulation_cex INV_GEN_PROC out_step print_to_solver3 from_solver3_ch  in
	    let _ = 
		if (!Flags.invariant_int && (!Flags.invariant_bool || !Flags.mode_inv))
		   then (
		     let ra = bool_imp_graph#set_new_graph simulation_value_hash in
		  	 let rb = ints_partial_order#sort simulation_value_hash in
		     if (ra || rb) then true else false) 
		else if (!Flags.invariant_bool || !Flags.mode_inv)
		      then (bool_imp_graph#set_new_graph simulation_value_hash)
		else if (!Flags.invariant_int)
		      then (ints_partial_order#sort simulation_value_hash )
		else failwith "Error" in
	    let _ =  print_to_solver3 solver#get#pop_string; (* POP Init of new vars for the step case + candidate*) in  
	      refinement_step := !refinement_step + 1;
	  ) else ( (* error *)
	    if (solver#get#result_is_error out_step) then
	      print_to_user_final ((Str.matched_string out_step)^"\n");
	      debug_proc INV_GEN_PROC None  ("SOLVER OUTPUT: "^out_step);
	      error_inv := true;	      
	  );
    end
  else
    begin
      debug_proc INV_GEN_PROC None ("STEP LOOP : Message received.\n");
      Globals.inv_gen_time_stop := (wtime());
      step_inv_stop := true;
      outer_loop_stop := true;
    end;
done;
     
if not !step_inv_stop && not !outer_loop_stop then
  begin
    if !cur_depth == 1 then send_to_induct:=false;
    first_time_round := false;
    print_to_solver3 solver#get#pop_string; (* POP Init of new vars for the step case + candidate*)
    print_to_solver3 solver#get#push_string; (***** PUSH  Init of real terms*****)
    Kind_support.persistent_step_asserts_concrete_inv 
      def_hash startdepth add (!cur_depth+1) from_checker_ch;
    print_to_solver3 solver#get#push_string; (***** PUSH Init of new vars*****)
    print_to_solver3 (New_vars.mk_nvr_eq_cmds (NUM !cur_depth));
    refinement_base := 0;
    cur_depth := !cur_depth + 1;
  end
else
  begin
    exit 0;
  end
 done;
    
    debug_proc INV_GEN_PROC (Some true) ("DONE")
   

  


	      
