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


(** A support module for the differet processes *)

(** 
@author Temesghen Kahsai

*)


open Flags
open Channels
open Globals
open Mpi
open Types

module type PROC_SUPPORT =
  sig
    val handle_cex: Types.foundvarstable -> int -> unit
    val handle_valid: int -> unit
    val handle_induct_cex: Types.foundvarstable -> unit
  end
      

module Helper =
struct
  (** Handle counterexamples for BMC process and INDUCT process *)
  let handle_cex foundvars k1 =
    let k_s = string_of_int (k1+1) in
    let _ = Globals.base_time_stop := (wtime()) in
    let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
    let property = Lus_convert_print.mk_property_string !Globals.prop_typed_stream in
    let bt_string = string_of_float base_time in 
      if !Flags.xml then (
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
	Kind_support.print_countermodel foundvars 0 k1);
      if !Flags.mpi_abort then (
	mpi_abort();
      ) else (  
	let _ = isend STOP step_proc 8 comm_world in
	  proc_size ==2 or 
	    (debug_proc BASE_PROC (Some true) "Sent a message to INV GEN.";
	     isend STOP 2 9 comm_world;true);
	  ()
      )

 (** Handle valid properties outcome *)
  let handle_valid kappa = 
    let k_s = string_of_int kappa in
    let _ = Globals.base_time_stop := (wtime()) in
    let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
    let bt_string = string_of_float base_time in 
    let property = Lus_convert_print.mk_property_string !Globals.prop_typed_stream in
      if !Flags.xml then (
	print_xml(Kind_support.print_resultProp_xml 
		    {result=VALID;
		     foundvars= None;
		     minstep=None;
		     maxstep=None;
		     induct_cex= None;
		     name= property;
		     k=k_s;
		     time=bt_string});
      ) else (
	print_to_user_final ("   PROPERTY = [ " ^ property  ^ " ]\n" ^
			     "   RESULT = VALID    \n" ^
			     "   K = "^k_s^"   \n"  ^
			     "   TIME (ms) = "^bt_string^"\n\n"));
      if !Flags.mpi_abort then (
	 mpi_abort()
	)else(
	  proc_size ==2 or 
	    (debug_proc BASE_PROC (Some true) "Sent a message to INV GEN.";
	     isend STOP 2 9 comm_world;true);
   ()
 )

(** *)
let handle_induct_cex cex =
  let _ = Globals.base_time_stop := (wtime()) in
  let base_time = !Globals.base_time_stop -. !Globals.base_time_start in
  let bt_string = string_of_float base_time in 
  let property = Lus_convert_print.mk_property_string !Globals.prop_typed_stream in
    match cex with
	None -> 
	  let k_s = "MAX_ITERATION" in
	    if !Flags.xml then (
	      print_xml(Kind_support.print_resultProp_xml 
			  {result=UNKNOWN;
			   foundvars= None;
			   minstep=None;
			   maxstep=None;
			   induct_cex= None;
			   name= property;
			   k=k_s;
			   time=bt_string});
	    ) else (
	      	print_to_user_final ("   PROPERTY = [ " ^ property  ^ " ]\n" ^
			     "   RESULT = UNKNOWN    \n" ^
			     "   K =  MAX ITERATIONS REACHED \n"  ^
			     "   TIME (ms) = "^bt_string^"\n\n"));
	    if !Flags.mpi_abort then(
	      mpi_abort();)
	    else
	      ( proc_size ==2 or 
		  (debug_proc BASE_PROC (Some true) "Sent a message to INV GEN.";
		   isend STOP 2 9 comm_world;true);
		()
	      )
      |	Some(induct_cex,global_k) ->
	  let property = Lus_convert_print.mk_property_string !Globals.prop_typed_stream in
	  if !Flags.xml then (
	    print_to_user_final ("INDUCTIVE COUNTEREXAMPLE NOT SUPPORTED IN XML YET.\n"));
	    print_to_user_final ("   PROPERTY = [ " ^ property  ^ " ]\n" ^
			     "   RESULT = UNKNOWN    \n" ^
			     "   K =  MAX INTERACTIONS REACHED \n"  ^
			     "   TIME (ms) = "^bt_string^"\n" ^ 
		             "   INDUCTIVE COUNTEREXAMPLE TRACE:\n" ^ induct_cex ^ "\n");	  
	  if !Flags.mpi_abort then(
	    mpi_abort();)
	  else
	    ( proc_size ==2 or 
		( debug_proc BASE_PROC None "Sent a message to INV GEN.";
		  isend STOP 2 9 comm_world;true);
		()
	    )
end

