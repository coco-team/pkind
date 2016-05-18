(** Kind-Inv: Offline invariant generator for lustre programs. Main entry point. *)

(**
@author Yeting Ge and Temesghen Kahsai

*)

open Types
open Exceptions
open Channels
open Globals


let solver = Globals.my_solver

(********************************************************************)
let print_copyright () =
  print_string (
   "\nOffline invariants generator for Lustre programs. (version "^Globals.version
  ^", build "^Globals.build^")\n"
  ^"* Copyright (c) 2007-2011 by the Board of Trustees of the University of Iowa.\n"
  ^"* All rights reserved.\n"
  ^"* \n"
  ^"* Redistribution and use in source and binary forms, with or without\n"
  ^"* modification, are permitted provided that the following conditions are met:\n"
  ^"*     * Redistributions of source code must retain the above copyright\n"
  ^"*       notice, this list of conditions and the following disclaimer.\n"
  ^"*     * Redistributions in binary form must reproduce the above copyright\n"
  ^"*       notice, this list of conditions and the following disclaimer in the\n"
  ^"*       documentation and/or other materials provided with the distribution.\n"
  ^"*     * Neither the name of the University of Iowa, nor the\n"
  ^"*       names of its contributors may be used to endorse or promote products\n"
  ^"*       derived from this software without specific prior written permission.\n"
  ^"*\n"
(*
  ^"* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY\n"
  ^"* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\n"
  ^"* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\n"
  ^"* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY\n"
  ^"* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n"
  ^"* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\n"
  ^"* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\n"
  ^"* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n"
  ^"* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\n"
  ^"* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.\n"
*)
  )



let catch_alarm x =
  print_to_user_final (solver#get#cc^"Signal caught: Timeout. Terminating.\n");
  exit x

let catch_term x =
  print_to_user_final (solver#get#cc^"Signal caught: Memory out. Terminating.\n");
  exit x

let catch_pipe x =
  print_to_user_final (solver#get#cc^"Signal caught: Broken pipe. The solver has unexpectedly closed.  Terminating.\n"
		       ^(match !Flags.set_my_solver with
			     YICES -> ""
			   | YICES_WRAPPER ->
			       solver#get#cc^"It is possible a formula exceeded the interactive yices buffer.\n"
			   | CVC3 -> (if !Flags.abs_mode then
					solver#get#cc^"It is possible CVC3 failed to instantiate a counterexample.\n"
					^solver#get#cc^"Try re-running with abstraction turned off.\n" else "")
			   | Z3 -> ""
			   | CVC4 -> (if !Flags.abs_mode then
					solver#get#cc^"It is possible CVC4 failed to instantiate a counterexample.\n"
					^solver#get#cc^"Try re-running with abstraction turned off.\n" else "")
			);
		      );
  exit x


(********************************************************************)
let start fn =
    begin
      match !Flags.set_my_solver with
        YICES ->
          failwith("YICES EXEC is not supported yet for generation of invariants.")
      | YICES_WRAPPER ->
	  begin
	   if(Solvers_path.yicesw_path = "no") then
	      (
		solver#set (new Solver_yices_cmdline.solver_yices_cmdline)
	      )else(
		solver#set (new Solver_yices.solver_yices)
	      );
	      end
      | CVC3 ->
          failwith("CVC3 is not supported yet for generation of invariants.")
      | CVC4 ->
	  failwith("CVC4 is not supported yet for generation of invariants.")
      | Z3->
	  failwith("Z3 is not supported yet for generation of invariants.")
      end;
      Flags.commentchar := solver#get#cc;
      if !Flags.do_scratch then
        begin
	    inv_ch := open_out (fn^"."^solver#get#file_extension^"_inv_offline")
        end;
	Kind_inv_loop.mainloop fn ;;




(********************************************************************)
let _ =
  let usage_msg = "Generate invariants for single node Lustre program.\nUsage: kind-inv [options] input_file" in
  let speclist = [
    ("-node", Arg.String (fun x -> Flags.user_specified_main_node_name := x),
     "\tCONTROL: User specified main node (default: the last node that contains a PROPERTY)");

    ("-inv_bool", Arg.Unit (fun () -> Flags.invariant_bool := true),
     "\tINVARIANT GENERATION: Do not generate boolean implication invariants. (default: off)");

    ("-inv_int", Arg.Unit (fun () -> Flags.invariant_int := true),
     "\tINVARIANT GENERATION: Do not generate integer less_or_equal invariants. (default: off)");

    ("-inv_mode", Arg.Unit (fun () -> Flags.mode_inv := true),
     "\tINVARIANT GENERATION: Do not generate invariants for mode variables. (default:off --- generate invariants for mode variables)");

    ("-state_inv", Arg.Unit (fun () -> Flags.state_inv := true),
     "\tINVARIANT GENERATION: Generate state invariants (default:off -- do not generate state invariants)");

    ("-rm_trivial_inv", Arg.Unit (fun () -> Flags.remove_trivial_invariants :=true ),
     "\tINVARIANT GENERATION: Remove trivial invariants (default: Leave trivial invariants)");

    ("-yices_exec", Arg.Unit (fun () -> Flags.set_my_solver := YICES),
     "\tSOLVER: Use Yices executable as solver (default: yicesw)");

    ("-solver_path", Arg.String (fun x -> Flags.solver_path := x;
				          Flags.gui:=true),
     "\tSOLVER: Specify the path to the solver. Used for KIND GUI. (default: specified by ./configure)");

    ("-scratch", Arg.Unit (fun () -> Flags.do_scratch := true),
     "\tOUTPUT: Produce files for debugging purposes. This option will produce 3 files (*_base, *_induct, *_inv). (default: Don't log to disk)");

    ("-quiet", Arg.Unit (fun () -> Flags.loud := false;
                                   Flags.final_cex_loud := false),
     "\tOUTPUT: Only return final answer (default: true)");

    ("-verbose", Arg.Unit (fun () -> Flags.loud := true;
                                     Flags.final_cex_loud := true),
     "\tOUTPUT: Return more details (default: false)");

    ("-version", Arg.Unit (fun () -> print_copyright()),
     "Print version & copyright information")
  ]
  in
  Arg.parse speclist start usage_msg
