(*
This file is part of the Kind verifier

* Copyright (c) 2007-2010 by the Board of Trustees of the University of Iowa, 
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


(** Non-Incremental online invariant generator *)

(**
@author Yeting 
@author Temesghen Kahsai

*)

open Types
open Flags
open Exceptions
open Channels
open Globals
open Mpi
open Util

exception EQUIV_CLS_STABLE
exception SOLVER_ERROR

let solver = Globals.my_solver
let toss x = () (* toss outputs *)

(** Print the invariant using the internal format of KIND *)
let print_invariant b_eqs b_imps i_eqs i_imps depth=
  let buf = Buffer.create 100 in
     Buffer.add_string buf "(define ASSERTIONS-INV :: (-> _nat bool) (lambda ( _M::nat) (ite (= _M _base) true " ;
    Buffer.add_string buf "( and";
    List.map(fun x ->   Buffer.add_string buf (Imp_graph.equ_invariant x);) b_eqs;
    List.map(fun x ->   Buffer.add_string buf (Imp_graph.imp_invariant x);) b_imps;
    List.map(fun x ->   Buffer.add_string buf (Imp_graph.int_eq_invariant x);) i_eqs;
    List.map(fun x ->   Buffer.add_string buf (Imp_graph.int_imp_invariant x);) i_imps; 
     Buffer.add_string buf "))))";
     (Buffer.contents buf);;  

let print_invariant_no_imp b_eqs b_imps i_eqs i_imps depth=
  let buf = Buffer.create 100 in
     Buffer.add_string buf "(define ASSERTIONS-INV :: (-> _nat bool) (lambda ( _M::nat) (ite (= _M _base) true " ;
    Buffer.add_string buf "( and";
    List.map(fun x ->   Buffer.add_string buf (Imp_graph.equ_invariant x);) b_eqs;
    List.map(fun x ->   Buffer.add_string buf (Imp_graph.int_eq_invariant x);) i_eqs;
    List.map(fun x ->   Buffer.add_string buf (Imp_graph.int_imp_invariant x);) i_imps; 
     Buffer.add_string buf "))))";
     (Buffer.contents buf);; 

let loop defdoc maxdepth def_hash pvars =
  let _ = debug_proc INV_GEN_PROC None ("MAIN.") in 

  (* generate defs for new vars of equalities. Yeting  *)
  let all_terms = Lus_convert_yc.get_all_def_terms () in
  let bool_sub_exprs, int_sub_exprs, float_sub_exprs = 
    Sub_exprs.sub_exprs all_terms Expr_util.filter_sub_exprs in

  (* generate new vars defs. Yeting *)
  let new_bool_var_doc = New_vars.bool_newvar_defs bool_sub_exprs in
  let new_int_var_doc =  New_vars.int_newvar_defs int_sub_exprs in

  (* Boolean invariants *)
  let bool_imp_graph =     
    new Imp_graph.bool_imp_graph (
      if (!Flags.invariant_bool) 
      then (New_vars.get_bool_nvrs ())
      else []
    )
  in

  (*Integer invariants *)
  let ints_partial_order = 
    new Partial_order.partial_order (
      if (!Flags.invariant_int) 
      then New_vars.get_int_nvrs ()
      else []
    ) 
  in
  (* end of new vars *)
    
  let nvar = solver#get#k_position_string in
  let add = Kind_support.get_add() in
  let nstart = solver#get#step_base_string in
  let startdepth = maxdepth + 1 in
  let from_checker_ch, from_solver3_ch = Kind_support.setup_solver3() in


  (* print definitions *)
  Kind_support.print_defs_to_solver3 from_solver3_ch from_checker_ch (defdoc^"\n");

 (* print definitions of new vars .   *)
  print_to_solver3 solver#get#push_string;
  Kind_support.print_defs_to_solver3 from_solver3_ch from_checker_ch (new_bool_var_doc^"\n");

 if (!Globals.is_inter && !Flags.mode_inv) then (
      List.iter (fun (v,lb,ub) -> 
		   let p, n = New_vars.mk_one_mode_candidate v lb ub in
		     Kind_support.print_defs_to_solver3 from_solver3_ch from_checker_ch (p^n)
		)(New_vars.get_interval_vars()));

  Kind_support.print_defs_to_solver3 from_solver3_ch from_checker_ch (new_int_var_doc^"\n");
 (* end of print definitions of new vars *)

  debug_proc INV_GEN_PROC None ("Begin induction:\n");
  (* print initial case *)
  print_to_solver3 solver#get#push_string; (***** PUSH  Init of real terms*****) 
  Kind_support.print_init 3 def_hash startdepth add from_checker_ch;

  (* print new variables assertions.   *)
  print_to_solver3 solver#get#push_string; (***** PUSH *****)
  print_to_solver3 (New_vars.mk_nvr_eq_cmds (NUM 0));
  (* print new variables assertions.   *)

  Kind_support.set_last_level_asserted (startdepth-1);


  let rec filter_imp_equiv_classes_one_round stepn_positions =
    debug_proc INV_GEN_PROC None ("INV GEN PROC:Filter");
    print_to_solver3 solver#get#push_string; 

    if (!Flags.invariant_bool)
    then 
      List.iter 
      (fun x-> print_to_solver3 x; )
      (bool_imp_graph#doc_of_stepn_asserts stepn_positions);

    if (!Flags.invariant_int)
    then
    List.iter 
      (fun x-> print_to_solver3 x; )
      (ints_partial_order#doc_of_stepn_asserts stepn_positions);
     
    let bool_imp_doc = 
      if !Flags.invariant_bool
      then (bool_imp_graph#doc_of_asserts ())
      else [] 
    in
 
    let int_imp_doc = 
      if !Flags.invariant_int
      then (ints_partial_order#doc_of_asserts ())
      else []
    in
   
    let imp_equiv_doc = Expr_util.mk_not_ands (bool_imp_doc@int_imp_doc)
    in
      if ("" = imp_equiv_doc) 
      then false
      else (
      print_to_solver3 imp_equiv_doc;
      print_to_solver3 (
        Lus_convert_yc.simple_command_string (
          QUERY(F_TRUE)));
          
      print_to_solver3 solver#get#done_string;

    let out1 = solver#get#get_output from_solver3_ch in
      if (solver#get#result_is_unsat out1) 
      then(
        print_to_solver3 solver#get#pop_string; (* PUSH 2 *)
	true)
    else if (solver#get#result_is_sat out1) 
    then(
      let simulation_value_hash = 
	solver#get#get_simulation_value_hash out1 
	  print_to_solver3 from_solver3_ch  in

      let changed = 
	if (!Flags.invariant_bool && !Flags.invariant_int)
	then (
	  let ra = bool_imp_graph#set_new_graph simulation_value_hash in
	  let rb = ints_partial_order#sort simulation_value_hash in
	    if (ra || rb) then true else false) 
	else if (!Flags.invariant_bool)
	then (bool_imp_graph#set_new_graph simulation_value_hash)
	else if (!Flags.invariant_int)
	then (ints_partial_order#sort simulation_value_hash )
	else failwith "Error"
      in
	print_to_solver3 solver#get#pop_string;
	if (changed ) 
	then ( 
	  filter_imp_equiv_classes_one_round stepn_positions 
	)
        else  false 
    )
    else ( (* error *)
      if (solver#get#result_is_error out1) then
      debug_proc INV_GEN_PROC None ("INV GEN PROC: SOLVER OUTPUT: "^out1);
      Globals.error := true;
      raise SOLVER_ERROR
    )
      )
  in
    (* some vars to control loops  *)
  let cur_depth = ref maxdepth  in
  let last_changed = ref !cur_depth in
  let stable = ref false in


while not !stable do
  while  not !Globals.stop do
    debug_proc INV_GEN_PROC None ("INV GEN PROC: - BASE LOOP  \n");
    (* Checking BASE *)
    print_to_solver3 solver#get#push_string; (***** PUSH *****)
    
    (* print the assertion of equiv classes.   *) 
    let bool_imp_doc =
      if (!Flags.invariant_bool)
      then  bool_imp_graph#doc_of_asserts()
      else []
    in
      
    let int_imp_doc =
      if (!Flags.invariant_int)
      then ints_partial_order#doc_of_asserts()
      else []
    in
           
    let equiv_imp_doc = Expr_util.mk_not_ands (bool_imp_doc@int_imp_doc) in
      print_to_solver3 equiv_imp_doc;
   
      if (equiv_imp_doc = "")
      then (print_invariant [] [] [] [] 1; exit 0 );
      
      let base_num = !cur_depth * add in
	debug_proc INV_GEN_PROC None ("INV GEN PROC: Asserting base case.\n");
	let assert_base = (F_EQ(POSITION_VAR(nstart),NUM(base_num),L_INT)) in
	  print_to_solver3 
	    (Lus_convert_yc.simple_command_string (ASSERT assert_base));
      
	  print_to_solver3 ( Lus_convert_yc.simple_command_string (QUERY(F_TRUE)));

    (* BASE check *)
     debug_proc INV_GEN_PROC None ("INV GEN PROC: Checking base case.\n");
    print_to_solver3 solver#get#done_string;
    (* finished BASE check *)
    
    let out1 = solver#get#get_output from_solver3_ch in
      if (solver#get#result_is_unsat out1) then
	begin (* base valid *)
	  debug_proc INV_GEN_PROC None ("INV GEN PROC: Valid base case - K NOT Stable.\n");
          print_to_solver3 solver#get#pop_string; (* PUSH 2 *)
	  
          if (!cur_depth ) > (!last_changed )  then 
	    debug_proc INV_GEN_PROC None ("INV GEN PROC: Valid base case - K Stable.\n");
	  stable := true;
	  Globals.stop := true;
	  
          Kind_support.persistent_step_asserts_concrete 
            def_hash startdepth add (!cur_depth+1) from_checker_ch;
	  cur_depth := !cur_depth + 1 ; 
	  
	end (* base valid *)
      else if (solver#get#result_is_sat out1) then
	begin (* base invlaid *)
          debug_proc INV_GEN_PROC None ("INV GEN PROC: Invalid base case - K NOT Stable.\n");
	  last_changed := !cur_depth;
	    (* get the values of nvrs.  *) 
	    let simulation_value_hash = solver#get#get_simulation_value_hash out1 print_to_solver3 from_solver3_ch  in
	      
	    let changed  = 
	      if (!Flags.invariant_int && !Flags.invariant_bool)
	      then (
		let ra = bool_imp_graph#set_new_graph simulation_value_hash in
		let rb = ints_partial_order#sort simulation_value_hash in
		  if (ra || rb ) then true else false )
	      else if (!Flags.invariant_bool)
	      then (bool_imp_graph#set_new_graph simulation_value_hash)
	      else if (!Flags.invariant_int)
	      then (ints_partial_order#sort simulation_value_hash)
	      else failwith "Error"
	    in
	      
              print_to_solver3 solver#get#pop_string;
              print_to_solver3 solver#get#safe_pop; (* PUSH 2 *)
              begin
		Globals.stop := not changed ;
		if(!Globals.stop ) 
		then (
		  pr (Expr_util.mk_not_ands (bool_imp_graph#doc_of_asserts() ));
		  pr "No changes while sat.\n";
		  failwith "global stop"; )
		  (*Globals.stop := true*)
              end
	end (* base invalid *)
      else
	begin
          (* BASE check = ERROR *)
          if (solver#get#result_is_error out1) then
          debug_proc INV_GEN_PROC None ("SOLVER OUTPUT: "^out1);
          Globals.error := true;
          Globals.stop := true
	end;
  done; (* main loop *)
  
  debug_proc INV_GEN_PROC None("INV GEN PROC: STABLE K.\n");
  stable := true;
  
done; (* main stable*)
    
    
    debug_proc INV_GEN_PROC None("INV GEN PROC: STABLE K - DOING INDUCTION.\n");
    
    print_to_solver3 solver#get#pop_string; 
    print_to_solver3 solver#get#pop_string; 
    (* Print new var defs *)
    print_to_both solver#get#push_string; (***** PUSH *****)
    print_to_solver3 (New_vars.mk_nvr_eq_cmds (POSITION_VAR(nvar)));
    (* assert new base *)
    let base_num = !cur_depth * add in
    let assert_base = (F_EQ(POSITION_VAR(nstart),NUM(base_num),L_INT)) in
      print_to_solver3 
	  (Lus_convert_yc.simple_command_string (ASSERT assert_base));
      (* print defs *)
      
      let stepn_positions =  
        List.map 
	  (fun x -> MINUS(POSITION_VAR(nvar),NUM(x))) 
	  (Util.n_to_m 1 (!cur_depth - 1))  in 
	
	List.iter (fun x -> 
		     Kind_support.def_assert_both1 def_hash "DEF" 
		       [PLUS(POSITION_VAR(nvar),NUM(x*add))]
		       !cur_depth from_checker_ch;) (Util.n_to_m 0 (!cur_depth - 1) ) ;
	
	if filter_imp_equiv_classes_one_round stepn_positions
	then ( 
	  let b_eqs,b_imps =
	    if (!Flags.invariant_bool)
	    then bool_imp_graph#eq_imp_graph()
	    else [],[]
	  in
	  let int_eqs,int_imps =
	    if (!Flags.invariant_int)
	    then ints_partial_order#eq_imp()
	    else [],[]
	  in
	    Globals.inv_gen_time_stop := (wtime());	
	    
	    debug_proc INV_GEN_PROC None("INV GEN PROC: Sending Invariant to STEP PROC.\n");		
	    
	    let invariant =
	      if !Flags.no_imp then 
		print_invariant_no_imp b_eqs b_imps int_eqs int_imps maxdepth
	      else 
	    print_invariant b_eqs b_imps int_eqs int_imps maxdepth in  
            let s_invariant = INV_FULL(invariant) in 
	      send s_invariant step_proc 89 comm_world;
	      
	)
	else (
	  pr "assert true;\n";
	);
	
	
