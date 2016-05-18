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

(** A module for integracting with Kind-AI *)

(**
@author Pierre-Loic Garoche 
@author Temesghen Kahsai

*)
open Types
open Globals
open Mpi

let kind_ai_cmd = Solvers_path.kind_ai_path
let args = " -seq -online -verbose-level -1 "

let main filename =
  if kind_ai_cmd = "undefined" then 
    ()
  else (
    let (proc_stdout, proc_stdin, proc_sterr)  = 
    Unix.open_process_full (kind_ai_cmd ^ args ^ filename) [||] in
  begin
    try
      while true do
	begin
	  let new_inv = input_line proc_stdout in
	  Format.fprintf Format.str_formatter 
	    "(define ASSERTIONS-INV :: (-> _nat bool) (lambda ( _M::nat) (ite (= _M _base) true %s)))" new_inv;
	  let invariant = Format.flush_str_formatter () in  
	  let s_invariant = INV_FULL(invariant) in 
	  Mpi.send s_invariant step_proc 89 comm_world
	end;
      done
  with End_of_file -> (
    (* let proc_status = Unix.close_process_full proc in *)
    exit 0)
  end
  )
    
