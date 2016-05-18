(** Incremental and Parallel Kind for verification of multiple properties.
    A front end that allow you to interact with pkind without going trough mpiexec.
*)


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
   "\nParallel K-Induction-based model checker (version "^Globals.version
  ^", build "^Globals.build^")\n")

let pkind_cmd = "pkind-main"  (* pkind binary*)

(********************************************************************)

(* Various options *)

let inv_gen = ref false
let kind_ai = ref false
let arg_node : string option ref = ref None
let arg_n: int option ref = ref None
let arg_no_multi = ref false
let arg_timeout : float option ref = ref None
let arg_k_incremental : int option ref = ref None
let arg_no_incremental = ref false
let arg_range : int option ref = ref None
let arg_mpi_abort = ref false
let arg_cvc4 = ref false
let arg_z3 = ref false
let arg_yices_exec= ref false
let arg_solver_path: string option ref = ref None
let arg_define_mod_div = ref false
let arg_compression = ref false
let arg_loop = ref false
let arg_flags: string option ref = ref None
let arg_quiet = ref false
let arg_verbose = ref false
let arg_induct_cex = ref false
let arg_scratch = ref false
let arg_only_inputs = ref false
let arg_dot = ref false
let arg_dotall = ref false
let arg_version = ref false
let arg_no_inlining = ref false
let arg_no_imp = ref false
let arg_naive = ref false
let arg_mode_inv = ref false
let arg_int_inv = ref false
let arg_bool_inv = ref false
let arg_state_inv = ref false
let arg_tg = ref false
let arg_sim_file = ref None
let arg_horn = ref false


let get_args () =
  let list =
    (if !inv_gen then ["-with-inv-gen"] else []) @
      (if !kind_ai then ["-with-kind-ai"] else []) @
      (match !arg_node with None -> [] | Some s -> ["-node " ^ s]) @
      (match !arg_n with None -> [] | Some i -> ["-n " ^ string_of_int i]) @
      (if !arg_no_multi then ["-no_multi"] else []) @
      (match !arg_timeout with None -> [] | Some x -> ["-timeout " ^ string_of_float x]) @
      (match !arg_k_incremental with None -> [] | Some x -> ["-k_incremental " ^ string_of_int x]) @
      (if !arg_no_incremental then ["-no_incremental"] else []) @
      (if !arg_mode_inv then ["-inv_mode"] else []) @
      (if !arg_int_inv then ["-inv_int"] else []) @
      (if !arg_bool_inv then ["-inv_bool"] else []) @
      (if !arg_state_inv then ["-inv_state"] else []) @
      (if !arg_mpi_abort then ["-mpi_abort"] else []) @
      (if !arg_z3 then ["-z3"] else []) @
      (if !arg_cvc4 then ["-cvc4"] else []) @
      (if !arg_yices_exec then ["-yices_exec"] else []) @
      (match !arg_solver_path with None -> [] | Some x -> ["-solver_path " ^ x]) @
      (if !arg_define_mod_div then ["-define_mod_div"] else []) @
      (if !arg_compression then ["-compression"] else []) @
      (if !arg_loop then ["-loop"] else []) @
      (match !arg_flags with None -> [] | Some x -> ["-flags \"" ^ x ^ "\""]) @
      (if !arg_quiet then ["-quiet"] else []) @
      (if !arg_verbose then ["-verbose"] else []) @
      (if !arg_induct_cex then ["-induct_cex"] else []) @
      (if !arg_scratch then ["-scratch"] else []) @
      (if !arg_only_inputs then ["-only_inputs"] else []) @
      (if !arg_dot then ["-dot"] else []) @
      (if !arg_dotall then ["-dotall"] else []) @
      (if !arg_tg then ["-tg"] else []) @
      (if !arg_horn then ["-horn"] else []) @
      (match !arg_sim_file with None -> [] | Some x -> ["-sim \"" ^ x ^ "\""]) @
      (if !arg_no_inlining then ["-no_inlining"] else [])
  in
  Array.of_list list

let start fn =
  let nb_proc =
    if (!arg_tg || (!arg_sim_file != None) || !arg_horn) then (
      0
    )else (if !arg_int_inv || !arg_bool_inv || !arg_mode_inv then
      3
    else(
      match !inv_gen, !kind_ai with
        | true, true -> 4
        | false, true
        | true, false -> 3
        | false, false -> 2)
  )
  in
  let arg = if nb_proc = 0 then
      (  Array.concat [[|pkind_cmd |]; get_args (); [|fn|]]
    )else(
      Array.concat [[| "mpiexec" ; "-n"; string_of_int nb_proc;  pkind_cmd |]; get_args (); [|fn|]]
      ) in
  let cmd = Array.fold_left (fun res s -> res ^ " " ^ s) "" arg in
  let (in_chan, out_chan) as proc = Unix.open_process cmd in
  try
    while true do print_endline (input_line in_chan); done
  with End_of_file -> (
      (*let proc_status = Unix.close_process proc in*)
      exit 5646)



let set refvar s = refvar := Some s
(********************************************************************)
let _ =
  let usage_msg = "PKIND -- Incremental and Parallel K-induction model checker for multiple property Lustre programs. \nUsage: pkind [options] input_file" in
  let speclist = [
    ("-with-kind-ai", Arg.Set kind_ai,
     "\tINV-GEN: Activate invariant generation based on abstract interpretation (default: off).\n" ^
     "\t\t\t         KIND-AI must have been installed and configured with './configure'."
    );
    ("-with-inv-gen", Arg.Set inv_gen,
     "\tINV-GEN: Activate invariant generation based on a template.\n"^
     "\t\t\t         It will generate invariants of type BOOL, INT and MODE (default: off)"
    );
    ("-inv_bool", Arg.Set arg_bool_inv,
     "\t\tINV-GEN: Generate only boolean implication invariants. (default: off)"
    );
    ("-inv_int", Arg.Set arg_int_inv,
     "\t\tINV-GEN: Generate integer less_or_equal invariants. (default: off)"
    );
    ("-inv_mode", Arg.Set arg_mode_inv,
     "\t\tINV-GEN: Generate invariants for mode variables. (default: off)"
    );
     ("-inv_state", Arg.Set arg_state_inv,
     "\t\tINV-GEN: Generate state invariants. (default: off)"
    );
    ("-tg", Arg.Set arg_tg,
     "  \t\tCONTROL: Generate test cases (default: off)"
    );
    ("-horn", Arg.Set arg_horn,
     "  \t\tCONTROL: Generate Monolythic Horn clauses (default: off)"
    );
    ("-sim", Arg.String (set arg_sim_file),
     "<input value file> \t\tCONTROL:  Simulate the Lustre code. Need to provide a csv file of input values. (default: off)"
    );
    ("-node", Arg.String (set arg_node),
     "<node> \t\tCONTROL: User specified main node (default: the last node that contains a PROPERTY)"
    );
    ("-n", Arg.Int (set arg_n),
     "<n> \t\tCONTROL: Stop after <n> iterations (default: 200)"
    );
    ("-no_multi", Arg.Set arg_no_multi,
     "\t\tCONTROL: Disable the incremental verification of multiple properties. (default: off)"
    );
    ("-timeout", Arg.Float (set arg_timeout),
     "<d> \t\tCONTROL: Set timeout to <d> (default: 100.00)"
    );
    ("-k_incremental", Arg.Int (set arg_k_incremental),
     "<n> \tCONTROL: Generate incremental invariants for the first <n> iterations (default: 200)"
    );
    ("-no_incremental", Arg.Set arg_no_incremental,
     "\tCONTROL: Generate non-incremental invariants (default: off)"
    );
    ("-mpi_abort", Arg.Set arg_mpi_abort,
     "\t\tPARALLELISM: Abort the MPI environment on termination (default: off)."
    );
    ("-cvc4", Arg.Set arg_cvc4,
     "\t\tSOLVER: Use CVC4 as background solver (default: yicesw)"
    );
    ("-yices_exec", Arg.Set arg_yices_exec,
     "\t\tSOLVER: Use Yices executable as background solver (default: yicesw)"
    );
    ("-solver_path", Arg.String (set arg_solver_path),
     "<path> \tSOLVER: Specify the path to the solver (default: specified by ./configure). Used for KIND GUI"
    );
    ("-no_inlining", Arg.Set arg_no_inlining,
     "\t\tOPT: Do not attempt variable inlining (default: off)"
    );
    ("-compression", Arg.Set arg_compression,
     "\t\tCOMPR: Include loop freeness constraints but not termination check (default: off)"
    );
    ("-loop", Arg.Set arg_loop,
     "\t\tCOMPR: Include loop freeness constraints + termination check (default: off)"
    );
    ("-flags", Arg.String (set arg_flags),
     "<flags> \tSOLVER: Pass string <flags> to solver command line (default: none)"
    );
    ("-quiet", Arg.Set arg_quiet,
     "\t\tOUTPUT: Only return final answer (default: on)"
    );
    ("-verbose", Arg.Set arg_verbose,
     "\t\tOUTPUT: Return more details (default: off)"
    );
    ("-induct_cex", Arg.Set arg_induct_cex,
     "\t\tOUTPUT: Print the current inductive counterexample (default: off)"
    );
    ("-scratch", Arg.Set arg_scratch,
     "\t\tOUTPUT: Produce files for debugging purposes\n" ^
     "\t\t\t        (<input file>_base, <input file>_induct, <input file>_inv) (default: off)"
    );
    ("-version", Arg.Unit (fun () -> print_copyright()),
     "\t\tPrint version and copyright information"
    )
  ]
  in
  Arg.parse speclist start usage_msg
