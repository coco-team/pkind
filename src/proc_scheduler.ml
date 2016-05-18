(*
This file is part of the Kind verifier

* Copyright (c) 2007-2011 by the Board of Trustees of the University of Iowa, 
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

(** Process scheduler *)

(** 
@author Temesghen Kahsai

*)

open Types
open Flags
open Exceptions
open Channels
open Globals
open Mpi



module Dispatch =
struct   
  (** Schedule processes *)
  let schedule filename proc_number = 
    if(proc_rank = base_proc) then (* Base process *)
      begin 
	Globals.base_time_start := (wtime());
	Base_proc.main filename;
      end
    else if(proc_rank=step_proc) then (* Inductive step process *)
      begin
	Globals.step_time_start := (wtime());
	Induct_proc.main filename;
      end
    else if (proc_rank = !kind_ai_proc) then (* Kind_AI process *)
      begin
    	Globals.kind_ai_time_start := (wtime());
    	Kind_AI_wrapper.main filename
      end
    else if proc_rank = !inv_gen_proc then (* Invariant generation process *)
      begin
    	Globals.inv_gen_time_start := (wtime());
    	let defdoc,maxdepth,def_hash, pvars = Defgen.start_invariant_generator filename in
    	if(!Flags.incremental) then (
    	  Incremental_inv_gen.produce_invariants defdoc maxdepth def_hash pvars;
    	) else (
    	  Inv_generator.loop defdoc maxdepth def_hash pvars; 
    	)
      end
    else raise (Wrong_number_of_proc (proc_number, proc_rank));

end  
  
  
  










