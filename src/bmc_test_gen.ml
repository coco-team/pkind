(** Test generation for multiple properties *)

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


let handle_cex properties foundvars k1 =
    let k_s = string_of_int (k1+1) in
    let _ = Globals.base_time_stop := (wtime()) in
    let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
    let property = Lus_convert_print.mk_property_string !Globals.prop_typed_stream in
    let bt_string = string_of_float base_time in
    Kind_support.printTestInput foundvars 0 k1
    (*   if !Flags.xml then (
	print_xml (Kind_support.print_resultProp_xml
		     {result=INVALID;
		      foundvars= Some foundvars;
		      minstep=Some 0;
		      maxstep=Some k1;
		      induct_cex= None;
		      name=properties;
		      k=k_s;
		      time=bt_string});
      ) else (
	print_to_user_final ("   PROPERTY = [ " ^ properties  ^ " ]\n" ^
			     "   RESULT = INVALID    \n" ^
			     "   K = "^k_s^"   \n" ^
			     "   TIME (ms) = "^bt_string^"\n" ^
			     "   COUNTEREXAMPLE TRACE : \n");
	Kind_support.print_countermodel foundvars 0 k1) *)

let multiProp sol =
  let _ = debug_proc BASE_PROC None "MULTI: MAIN LOOP." in
  let _ = debug_proc BASE_PROC None ("MULTI: Startdepth: " ^ string_of_int (sol.startdepth) ) in
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

(*   let _ = print_to_user_final("\n\nThere are "^string_of_int(List.length named_prop)^" property(ies) to be checked.\n") in
  let _ = print_to_user_final("PROPERTIES TO BE CHECKED: [") in
  let _ = List.iter(fun x ->  (print_to_user_final(Multi_prop_util.get_real_prop_name (x)^" "))) named_prop in
  let _ = print_to_user_final("]\n") in

     *)
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
  let first_time_n_values = (Array.to_list (Array.init (!k_inc-1) (fun x -> x+1))) in
  let final_position = 0 in

 while  (!k_inc <= !Flags.maxloops && not !local_base_stop) do
   let k = !k_inc in
   let k1 = k-1 in
   let k_s = string_of_int k in
   let _ = debug_proc BASE_PROC (Some true) ("MULTI: Checking k="^k_s^" . ") in

   (* handle assertions *)
   let _ =
     if Lus_assertions.assertions_present() then
       begin (* handle assertions *)
	 let _ = debug_proc BASE_PROC None "MULTI: Printing assertion." in
	   print_to_solver (Lus_convert_yc.simple_command_string
	       (ASSERT(
		  F_PRED(solver#get#assertions,[NUM(sol.add*k1)]))));
	   if !local_firsttime then
	     for i= 0 to k1-1 do
	       print_to_solver (
		 Lus_convert_yc.simple_command_string
                   (ASSERT(F_PRED(solver#get#assertions,[NUM(sol.add*i)]))));
	       debug_proc BASE_PROC None "MULTI: Done printing assertion ";
	     done
       end
   in
   let _ = print_to_solver solver#get#push_string in
   let impl_premise = F_EQ(POSITION_VAR(sol.nstart),NUM(sol.add*k1),L_INT) in
   let impl_result =
     if !local_firsttime && k > 1 then
       begin
       let _ = debug_proc BASE_PROC None "MULTI: Before" in
	 List.fold_right (fun p p_acc ->
			    F_AND(
			      List.fold_left (fun acc x  ->
						F_AND(F_PRED(p,[NUM(sol.add*x)]), acc)) (F_PRED (p,[NUM(0)])) first_time_n_values, p_acc))
	   !unsolved_prop_list F_TRUE
       end
     else
     let _ = debug_proc BASE_PROC None "MULTI: After" in
       List.fold_left (fun p_acc p ->
			 F_AND(F_PRED(p,[NUM(final_position)]), p_acc)) F_TRUE !unsolved_prop_list
   in
     print_to_solver(Lus_convert_yc.simple_command_string (ASSERT(F_NOT(F_IMPL(impl_premise,impl_result)))));
     let _ = print_to_solver ( Lus_convert_yc.simple_command_string (QUERY(F_TRUE))) in
     let _ = print_to_solver solver#get#done_string in

let out_base = solver#get#get_solver_output BASE_PROC sol.from_solver_ch in
  if (solver#get#result_is_unsat out_base) then
    begin (* base valid *)
      let _ = debug_proc BASE_PROC (Some true) "MULTI: Valid base case." in
      let _ = print_to_solver solver#get#pop_string in
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

	(* We classify the properties in SAT and UNSAT from the value ID that we get from the counterexample *)
	if !local_firsttime then (
	  let _ = debug_proc BASE_PROC None ("MULTI: List of properties before filtering up to the depth:") in
	  let _ = debug_prop_id BASE_PROC !sat_id_prop_list in
	  let sat_id_found, unsat_id_found = Multi_prop_util.filter_props !sat_id_prop_list foundvars k1 in
	    sat_id_prop_list := sat_id_found;
	    unsat_id_prop_list := unsat_id_found;
	    let _ = debug_proc BASE_PROC None ("MULTI: List of invalid props up to the depth:") in
	      debug_prop_id BASE_PROC !sat_id_prop_list;
	)else(
	  sat_id_prop_list :=
	    List.filter (fun id -> Multi_prop_util.is_false
			   (Hashtbl.find foundvars (id,0))) !sat_id_prop_list;
	  unsat_id_prop_list :=
	    List.filter (fun id -> Multi_prop_util.is_true
			   (Hashtbl.find foundvars (id,0))) !unsat_id_prop_list
	);


	(*We update the VAR of the properties and we also update the list of unsolved properties *)
	let _ = unsat_var_prop_list := List.map (fun x -> (Tables.get_varinfo_name x)) !unsat_id_prop_list in
	let _ = sat_var_prop_list :=  List.map (fun x -> (Tables.get_varinfo_name x)) !sat_id_prop_list in
	let _ = unsolved_prop_list := List.filter(fun x ->  not (List.mem x !sat_var_prop_list)) !unsolved_prop_list in
	let _ = invalid_properties := List.append !invalid_properties (List.map (fun x -> Multi_prop_util.get_real_prop_name x) !sat_var_prop_list) in
	let _ = invalid_var_prop := List.append !invalid_var_prop !sat_var_prop_list in

	let _ =  debug_proc BASE_PROC None ("MULTI: List of invalid properties. ID and VAR: ") in
	let _ =  debug_prop_id BASE_PROC !sat_id_prop_list in
	let _ =  debug_prop_var BASE_PROC !sat_var_prop_list in
	let _ =  debug_proc BASE_PROC None ("MULTI: List of valid properties. ID and VAR:  ") in
	let _ =  debug_prop_id BASE_PROC !unsat_id_prop_list in
	let _ =  debug_prop_var BASE_PROC !unsat_var_prop_list in

	       (* Check if there are invalid properties *)
	if (List.length !sat_id_prop_list!=0) then(
	       (* Update the real name of the properties.*)
	    let _ = debug_proc BASE_PROC None "MULTI: DONE Updating list of properties " in
	    let properties =  List.fold_left (fun acc x -> (Multi_prop_util.get_real_prop_name(x) ^ " " ^ acc)) "" !sat_var_prop_list  in
	        handle_cex properties foundvars k1);

	if (List.length !unsolved_prop_list == 0) then(
		Multi_prop_util.print_summary !valid_properties !invalid_properties;
		local_base_stop := true)
	else (print_to_solver solver#get#pop_string);
		  debug_proc BASE_PROC None "Updating the prop ids";
		  sat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) !unsolved_prop_list;
		  unsat_id_prop_list := List.map (fun x -> Tables.varid_lookup x) !unsolved_prop_list;
		  local_firsttime := false;
	end (* base invalid *)
     else
       begin
         if (solver#get#result_is_error out_base) then
           print_to_user_final ((Str.matched_string out_base)^"\n");
           debug_proc BASE_PROC None ("SOLVER OUTPUT: "^out_base);
	   	   Globals.base_time_stop := (wtime());
	   	   base_error := true;
           local_base_stop := true
       end;

(*Check timeout*)

    if ((wtime()) -. !Globals.base_time_start) >= !Flags.timeout then (
      Globals.base_time_stop := (wtime());
      let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
      let bt_string = string_of_float base_time in
      local_base_stop := true;
      print_string "TIMEOUT");
(* 	if !Flags.xml then (
	  let prop_names =  Multi_prop_util.mk_prop_names !unsolved_prop_list in
	  print_xml (Kind_support.print_resultProp_xml
		       {result=TIMEOUT;
				foundvars=None;
				minstep=None;
				maxstep=None;
				induct_cex= None;
				name=prop_names;
				k="unknown";
				time=bt_string});
	  print_xml ("</Results>")
	) else(
	  print_to_user_final("\n\n++++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
	  print_to_user_final ("                       TIMEOUT                           \n");
	  print_to_user_final("++++++++++++++++++++++++++++++++++++++++++++++++++++++\n\n");
	  )); *)
 done (* main loop *)





(** Initialization *)
let init_baseProc filename =
  let defdoc,maxdepth,def_hash,no_stateful,pvars,prop_list = Defgen.start filename in
  let add = Kind_support.get_add() in
  let nstart = solver#get#step_base_string in
  let from_checker_ch, from_solver_ch = Kind_support.setup_solver1() in

   (* if no stateful vars, then cancels loopfree mode *)
    if no_stateful then( loopfree_mode := false; termination_check := false);
    if (!termination_check || !loopfree_mode) && not !abs_mode then (
      static_path_compression.(base_abstr) <- true;
      static_path_compression.(step_abstr) <- true);

    (* Needed for refinement*)
    if !checker_mode then print_to_checker solver#get#checker_setup_string;

    (* Check if to ignore the startdepth *)
    let startdepth = if !Flags.no_startdepth then 1 else maxdepth + 1 in
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
    Globals.base_time_start := (wtime());
    (* If no multi is specified do only single property verification *)
    if !Flags.no_multi then (
      debug_proc BASE_PROC (Some true) "Single property verification by option no_multi.";
      Single_test_gen.singleProp sol
    )else (
 (* If only single property do single BMC, otherwise do multi BMC (i.e. incremental verification)*)
    	if List.length sol.prop_list == 1 then
     	 (debug_proc BASE_PROC (Some true) "Single condition test generation";
      	 Single_test_gen.singleProp sol
      	) else (
			debug_proc BASE_PROC (Some true) "Multiple properties verification.";
		multiProp sol
      	)
    )
