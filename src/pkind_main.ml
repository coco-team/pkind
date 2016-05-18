(** Incremental and Parallel Kind for verification of multiple properties.  Main entry point. *)

(**
@author Temesghen Kahsai

*)

open Types
open Exceptions
open Channels
open Globals


let solver = Globals.my_solver

(********************************************************************)
let print_copyright () =
  print_string (
      "\nIncremental and Parallel K-Induction-based model checker (version "^Globals.version
      ^", build "^Globals.build^")\n")


(********************************************************************)
let catch_alarm x =
  print_to_user_final (solver#get#cc^"Signal caught: Timeout. Terminating.\n");
  exit x

let catch_term x =
  print_to_user_final (solver#get#cc^"Signal caught: Memory out. Terminating.\n");
  exit x

let catch_pipe x =
  print_to_user_final (solver#get#cc^"Signal caught: Broken pipe. The solver has unexpectedly closed. Terminating.\n"
                       ^(match !Flags.set_my_solver with
                           YICES -> ""
                         | YICES_WRAPPER ->
                            solver#get#cc^"It is possible a formula exceeded the interactive yices buffer.\n"
                         | Z3 -> ""
                         | CVC4 -> (if !Flags.abs_mode then
                                      solver#get#cc^"It is possible CVC4 failed to instantiate a counterexample.\n"
                                      ^solver#get#cc^"Try re-running with abstraction turned off.\n" else ""))
		      );
  exit x


module PS = Proc_scheduler.Dispatch (* The process scheduler *)

(********************************************************************)
let inv_gen = ref false
let kind_ai = ref false

let start fn =
  begin
    match !Flags.set_my_solver with
        YICES ->
          solver#set (new Solver_yices_cmdline.solver_yices_cmdline)
      | YICES_WRAPPER ->
	     begin
	    (* In case the yices warpper is not available switch to yices command line version *)
	    if(Solvers_path.yicesw_path = "no") then
	      (solver#set (new Solver_yices_cmdline.solver_yices_cmdline)
	      )else(
		        solver#set (new Solver_yices.solver_yices)
	      );
	     end
      | CVC4 -> solver#set (new Solver_cvc4.solver_cvc4)
      | Z3 -> solver#set (new Solver_z3.solver_z3)
      end;

    Flags.commentchar := solver#get#cc;

    (* Store the commmands sent to the solver in auxilary files, i.e. for debugging purposes.*)
    if !Flags.do_scratch then(
      if proc_size = 0 || proc_size = 1 then (
        base_ch := open_out (fn^"."^solver#get#file_extension^".debug");
      )else
        if proc_size = 2 then (
          base_ch := open_out (fn^"."^solver#get#file_extension^"_base");
          induct_ch := open_out (fn^"."^solver#get#file_extension^"_induct");
          extra_ch := open_out (fn^"."^solver#get#file_extension^"_extra");
	)else(
	  base_ch := open_out (fn^"."^solver#get#file_extension^"_base");
       induct_ch := open_out (fn^"."^solver#get#file_extension^"_induct");
       inv_ch := open_out (fn^"."^solver#get#file_extension^"_inv");
       extra_ch := open_out (fn^"."^solver#get#file_extension^"_extra");
	)
    );

    if !inv_gen then (Flags.invariant_bool := true;
                      Flags.invariant_int := true;
                      Flags.mode_inv := true);

    (match !inv_gen, !kind_ai with
     | true, true -> (
       inv_gen_proc := 2;
       kind_ai_proc := 3)
     | false, true -> (
       inv_gen_proc := -1;
       kind_ai_proc := 2)
     | true, false -> (
       inv_gen_proc := 2;
       kind_ai_proc := -1)
     | false, false -> ());

    (* Schedule processes *)
    if !Flags.tg then (
       Bmc_test_gen.main fn
    )else if !Flags.sim then (
        Interpreter_loop.main fn
    )else if !Flags.horn then (
      Horn.main fn
    )
    else (
      PS.schedule fn proc_size
    );;

(********************************************************************)
let _ =
  let usage_msg = "PKIND -- Incremental and parallel k-induction model checker for the verification of multiple property Lustre programs.
                   \nUsage: mpiexec -np [2 or 3] pkind-main [<options>] <input file>" in
  let speclist = [
    ("-with-inv-gen", Arg.Set inv_gen,

     "\tActivate INVARIANT GENERATION based on a template. It will generate invariants of type BOOL and INT (default: off)");

    ("-with-kind-ai", Arg.Set kind_ai,
     "\tActivate INVARIANT GENERATION based on abstract interpretation (default: off). KIND-AI must have been installed and configured with './configure'.");

    ("-inv_bool", Arg.Unit (fun () -> Flags.invariant_bool := true),
     "\tINVARIANT GENERATION: Do not generate boolean implication invariants. (default: True)");

    ("-inv_int", Arg.Unit (fun () -> Flags.invariant_int := true),
     "\tINVARIANT GENERATION: Do not generate integer less_or_equal invariants. (default: True)");

    ("-inv_mode", Arg.Unit (fun () -> Flags.mode_inv := true),
     "\tINVARIANT GENERATION: Do not generate invariants for mode variables. (default: True --- generate invariants for mode variables)");

    ("-inv_state", Arg.Unit (fun () -> Flags.state_inv := true),
     "\tINVARIANT GENERATION: Generate state invariants. (default: False -- do not generate state invariants)");

    ("-tg", Arg.Unit (fun () -> Flags.tg := true;
                                  Flags.print_all_vars := true;
                                  Flags.xml := false),
     "\tCONTROL: Test Generation (default: False)");

    ("-horn", Arg.Unit (fun () -> Flags.horn := true),
     "\tCONTROL: Generate Horn Clauses3 (default: False)");

    ("-sim", Arg.String (fun x -> Flags.sim_filename := x;
			        Flags.sim := true),
     "\tSpecify the filename of csv to simulate the Lustre program"
    );

    ("-node <node>", Arg.String (fun x -> Flags.user_specified_main_node_name := x),
     "\tCONTROL: User specified main node (default: the last node that contains a PROPERTY)");

    ("-n", Arg.Int (fun x -> Flags.maxloops := x),
     "\tCONTROL: Stop after <n> iterations (default: 200)");

    ("-no_multi", Arg.Unit (fun () -> Flags.no_multi := true),
     "\tCONTROL: Disable the incremental verification of multiple properties. (default: off)");

    ("-timeout", Arg.Float (fun x -> Flags.timeout := x),
     "\tCONTROL: Set timeout (default: 100.00)");

    ("-k_incremental <n>", Arg.Int (fun x -> Flags.k_incremental := x+1),
     "\tINVARIANT GENERATION: Generate incremental invariants for the first <n> iterations (default: 200)");

    ("-no_incremental", Arg.Unit (fun () -> Flags.incremental := false),
     "\tINVARIANT GENERATION: Generate non-incremental invariants (default: off --- generate incremental invariants)");

    ("-mpi_abort", Arg.Unit (fun () -> Flags.mpi_abort := true),
     "\tPARALLELISM: Abort the MPI environment on termination (default: off). Useful when the solver returns with an answer but the environment is not terminated yet");

    ("-cvc4", Arg.Unit (fun () -> Flags.set_my_solver := CVC4),
     "\tSOLVER: Use CVC4 as background solver (default: yicesw)");

    ("-yices_exec", Arg.Unit (fun () -> Flags.set_my_solver := YICES),
     "\tSOLVER: Use Yices executable as background solver (default: yicesw)");

    ("-z3", Arg.Unit (fun () -> Flags.set_my_solver := Z3),
     "\tSOLVER: Use CVC4 as background solver (default: yicesw)");

    ("-solver_path <path>", Arg.String (fun x -> Flags.solver_path := x; Flags.gui:=true),
     "\tSOLVER: Specify the path to the solver (default: specified by ./configure). Used for KIND GUI");

    ("-no_inlining", Arg.Unit (fun () ->
                               Flags.aggressive_inlining := 0;
                               Flags.inlining_mode := false),
     "\tOPT: Do not attempt variable inlining (default: off)");

    ("-define_mod_div", Arg.Unit (fun () -> Flags.define_mod_div := true),
      "\tSOLVER: Include definitions for mod & div (may be incomplete) (default: off)");

    ("-compression", Arg.Unit (fun () -> Flags.loopfree_mode := true),
     "\tCOMPR: Include loop freeness constraints but not termination check (default: off)");

    ("-loop", Arg.Unit (fun () -> Flags.loopfree_mode := true;
                                  Flags.termination_check := true),
     "\tCOMPR: Include loop freeness constraints + termination check (default: off)");

    ("-flags", Arg.String (fun x -> Flags.solverflags := x),
     "\tSOLVER: Pass string <flags> to solver command line (default: n/a)");

    ("-xml", Arg.Unit (fun x -> Flags.xml := true),
     "\tOUTPUT: Generate results in XML format (default: off)");

    ("-quiet", Arg.Unit (fun () -> Flags.loud := false;
                                   Flags.final_cex_loud := false),
     "\tOUTPUT: Only return final answer (default: on)");

    ("-verbose", Arg.Unit (fun () -> Flags.loud := true;
                                     Flags.final_cex_loud := true),
     "\tOUTPUT: Return more details (default: off)");

    ("-induct_cex", Arg.Unit (fun () -> Flags.inductive_cs := true),
     "\tOUTPUT: Print the current inductive counterexample (default: off)");

    ("-scratch", Arg.Unit (fun () -> Flags.do_scratch := true),
     "\tOUTPUT: Produce files for debugging purposes (<input file>_base, <input file>_induct, <input file>_inv) (default: off)");

    ("-only_inputs", Arg.Unit (fun () -> Flags.print_all_vars := false),
     "\tOUTPUT: Only print inputs in counterexamples (default: off)");

    ("-dot", Arg.Unit (fun () -> Flags.print_dot_one := true;
                                 Flags.abs_mode := true;
                                 Flags.var_defs_mode := true;
                                 Flags.loud := false),
     "\tOUTPUT: Print dot graph of dependencies (default: off)" );

    ("-dotall", Arg.Unit (fun () -> Flags.print_dot_all := true;
                                    Flags.abs_mode := true;
                                    Flags.var_defs_mode := true),
     "\tOUTPUT: Output all abstraction dependency graphs to graphXXX.dot (default: off)");

    ("-version", Arg.Unit (fun () -> print_copyright()),
     "\tPrint version and copyright information")
  ]
  in
  Arg.parse speclist start usage_msg
