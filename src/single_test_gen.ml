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


(** Defining some variables *)
let local_firsttime = ref true
let final_position = 0
let local_base_stop = ref false

let handle_cex foundvars k1 =
    let k_s = string_of_int (k1+1) in
    let _ = Globals.base_time_stop := (wtime()) in
    let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
    let property = Lus_convert_print.mk_property_string !Globals.prop_typed_stream in
    let bt_string = string_of_float base_time in
	print_string (Kind_support.printTestInputOracle foundvars 0 k1)
    (* print_string (Kind_support.printTestInputOracle foundvars 0 k1) *)
      (* if !Flags.xml then (
	print_xml (Kind_support.print_resultProp_xml
		     {result=INVALID;
		      foundvars= Some foundvars;
		      minstep=Some 0;
		      maxstep=Some k1;
		      induct_cex= None;
		      name=property;
		      k=k_s;
		      time=bt_string});
      ) else (
	print_to_user_final ("   PROPERTY = [ " ^ property  ^ " ]\n" ^
			     "   RESULT = INVALID    \n" ^
			     "   K = "^k_s^"   \n" ^
			     "   TIME (ms) = "^bt_string^"\n" ^
			     "   COUNTEREXAMPLE TRACE : \n");
	Kind_support.print_countermodel foundvars 0 k1) *)


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
	  UNSAT
      end (* base valid *)
    else if (solver#get#result_is_sat out_base) then
      begin (* base invalid *)
	let _ = debug_proc BASE_PROC (Some true) "Invalid base." in
	let basestep = if !local_firsttime then BASE_INIT else BASE in
	let foundvars = solver#get#get_cex BASE_PROC out_base print_to_solver sol.from_solver_ch in
	let _ = debug_proc BASE_PROC None ("checking absmode "^(string_of_int (Kind_refine.get_num_abstract base_abstr))) in
	let _ = print_to_solver solver#get#safe_pop in
	let _ = debug_proc BASE_PROC None ("Invalid at K ="^k_s^".\n") in
	  handle_cex foundvars k1;
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
  let _ = debug_proc BASE_PROC (Some true) ("Checking k="^k_s^". No message received.") in
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
	  debug_proc BASE_PROC None "Has assertions, Done. ";
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
  let _ = print_to_solver ( Lus_convert_yc.simple_command_string (QUERY(F_TRUE))) in
  let _ = print_to_solver solver#get#done_string in
    k



(** Single property verification *)
let singleProp sol =
  (* Print initial case *)
  let _ = print_to_solver solver#get#push_string in
  let _ = Kind_support.print_initialization sol.def_hash sol.startdepth sol.add sol.from_checker_ch in
  let k_inc = ref sol.startdepth in
  let first_time_n_values = (Array.to_list (Array.init (!k_inc-1) (fun x -> x+1))) in

    (*k-induction loop*)
  let local_time = wtime() in
    while (not !local_base_stop) do
      if ((wtime()) -. local_time) >= !Flags.timeout then (
       failwith ("TIMEOUT"))
      else(
        let _ = debug_proc BASE_PROC None "MAIN LOOP." in
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
	      local_firsttime := false;
	      incr k_inc

	  |ERROR ->
	     local_base_stop := true;
      )
    done (* main loop *)
