(*
This file is part of the Kind verifier

* Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
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

(** Path Compression Formulas & Termination Check*)

(** {6 Functions} *)

(** [general_compression_constraint startdepth add dest start k1 pos] prints out the appropriate path compression formula C(i..j) via [dest].  [base_pos] is a string for the base position, [start] is the point at which to start the compression (i), while [k1] is the point at which to end the compression (generally [k]-1 from the main loop).  [startdepth] is there the induction started. Used when there are no abstracted compression variables. *)
val general_compression_constraint : 
  int -> Types.addtype -> (string -> unit) -> int -> int -> string -> unit 

(** [abstracted_compression_constraint startdepth add dest start k1 pos] prints out the appropriate path compression formula C(i..j) via [dest].  [base_pos] is a string for the base position, [start] is the point at which to start the compression (i), while [k1] is the point at which to end the compression (generally [k]-1 from the main loop).  [startdepth] is there the induction started. Used if any abstraction variables are still abstracted. *)
val abstracted_compression_constraint :
  int -> Types.addtype -> (string -> unit) -> int -> int -> string -> unit

(** Performs the full termination check.  [termination_check def_hash startdepth k_step_size firststep add newly_refined_vars from_solver_ch from_checker_ch]
may perform refinements and can raise {!Exceptions.Reachable_space_explored}, indicating an end to the main loop. *)
val termination_check :
  Types.defhashtable -> int -> int -> bool -> Types.addtype -> (Types.idtype list ref) -> int -> in_channel -> in_channel -> unit
