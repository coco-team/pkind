(** Kind simulator *)

(**
@author Temesghen Kahsai

*)

open Types
open Exceptions
open Channels
open Globals

exception STOP_INTERACT

let solver = Globals.my_solver

(** Defining some variables *)
let local_firsttime = ref true
let first_interact = ref true

(** Return a list of input variables*)
let get_internal_id_vars () =
  Hashtbl.fold (fun i (n,v,t,c) acc  ->
		match c with
		  INPUT ->
		  let internal_name = Tables.get_varinfo_name i in
		  if (Tables.varid_lookup_interval internal_name = -1) then acc
		  else
		    ((Tables.varid_lookup_interval internal_name),t)::acc
		| _ -> acc
	       )(Tables.get_varinfo()) []

(** Get User input*)
let user_input hint quit_command =
  print_string hint;
  let input =  read_line ()  in
  let quit_cmd  = quit_command in
  if (input = quit_cmd)
  then (print_to_user_final "DONE\n"; exit 0)
  else input

(** A process helper module*)
module HL = Sim_support.Helper

(** Get the result from the solver*)
let get_bmc_result sol k =
  let k1 = k-1 in
  let k_s = string_of_int k in
  let out_base = solver#get#get_solver_output BASE_PROC sol.from_solver_ch in
  if (solver#get#result_is_unsat out_base) then
    begin (* base valid *)
      let _ = print_to_solver solver#get#safe_pop in
      let _ = debug_proc BASE_PROC (Some true) "UNSAT" in
      let _ = print_to_solver solver#get#pop_string in
      UNSAT
    end (* base valid *)
  else if (solver#get#result_is_sat out_base) then
    begin (* base invalid *)
      let _ = debug_proc BASE_PROC (Some true) "SAT" in
      let foundvars = solver#get#get_cex BASE_PROC out_base print_to_solver sol.from_solver_ch in
      if !Flags.xml then
        (print_string (Kind_support.printTestInputOracle foundvars 0 k1))
      else(HL.handle_cex foundvars k1);
      SAT
    end (* base invalid *)
  else
    begin
      print_to_user_final ("Abort in "^k_s^" base due to incompleteness or error.\n");
      if (solver#get#result_is_error out_base) then
        print_to_user_final ((Str.matched_string out_base)^"\n");
      let _ = debug_proc BASE_PROC None ("SOLVER OUTPUT: "^out_base) in
      ERROR
    end


(** Prepare the transition system and the property  *)
let  mk_trans_and_prop sol =
  let k = ref 0 in
  if !Flags.sim then(
    let all_buf, k_length = HL.generate_Input_Constraint k in
    k := k_length;
    for i=0 to k_length do
      Kind_support.def_assert_both1 sol.def_hash "DEF" [NUM(sol.add*i)] i sol.from_checker_ch;
     done;
    print_to_solver(Buffer.contents all_buf)
  ) else (failwith ("You need to specify a file that contains the input values"));

  if Lus_assertions.assertions_present() then
    begin
      let _ = debug_proc BASE_PROC None "Has assertion." in
      for i= 0 to !k do
        print_to_solver (Lus_convert_yc.simple_command_string(ASSERT(F_PRED(solver#get#assertions,[NUM(sol.add*i)]))));
      done;
      debug_proc BASE_PROC None "Has assertions, Done. ";
    end;
  let _ = print_to_solver solver#get#push_string  in
  print_to_solver ( Lus_convert_yc.simple_command_string (QUERY(F_TRUE)));
  print_to_solver solver#get#done_string;
  !k


(** Single property verification *)
let singleProp sol =
  (* Print initial case *)
  debug_proc BASE_PROC (Some true) "Asserting the TS";
  let k = mk_trans_and_prop sol in
  let result_bmc = get_bmc_result sol k in
  match result_bmc with
    SAT -> ()
    |_ -> raise STOP_INTERACT



(** Initialization *)
let init_baseProc filename =
  let defdoc,maxdepth,def_hash,no_stateful,pvars,prop_list = Defgen.start filename in
  let add = Kind_support.get_add() in
  let nstart = solver#get#step_base_string in
  let startdepth = maxdepth + 1 in
  let from_checker_ch, from_solver_ch = Kind_support.setup_solver1() in
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
  let input_vars_internal = get_internal_id_vars () in
  let input_vars_type = List.map (fun (x,y) -> (Tables.varid_to_orginal_name x), (Lus_convert_print.type_string y)) input_vars_internal in
  let input_vars_names = List.map (fun (x,y) -> (Tables.varid_to_orginal_name x)) input_vars_internal in
  singleProp sol




    (* print_to_user_final ("\nEnter input value in the following format:  [x=0; y=true; .... ;z=1])\n"); *)
    (* print_to_user_final("Available input variables for [" ^ filename ^ "] :\n\n"); *)
    (* print_to_user_final("-----------------------\n"); *)
    (* List.iter (fun (x,y) -> print_to_user_final("|   "^ x ^ " [of type " ^ y ^ "] \n")) input_vars_type; *)
    (* print_to_user_final("-----------------------\n\n"); *)
    (* print_to_user_final ("Iteration up to K = " ^ string_of_int(!Flags.maxloops)) *)

    (* while true do *)
    (*     if !first_interact then ( *)
    (*       for i=1 to !Flags.maxloops do *)
    (*         user_input ("\nEnter value for input variables at K =" ^ string_of_int(i) ^ "\n") "q" *)
    (*       done; *)
    (*     ) else ( *)
    (*       user_input ("\nEnter value for input variables at K =" ^ string_of_int(!k_inc) ^ " OR 'q' to quit.\n") "q"; () *)
    (*     ); *)
    (*     HL.check_valid_input input_value; *)
    (* done *)
