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

(** Abstraction Refinement logic *)

(** {6 Functions} *)

(** Initalize values *)
val set_num_abstract : unit -> unit

(** return the number abstract for either base (0) or step (1) *)
val get_num_abstract : int -> int

(** Initialize values *)
val set_not_fully_refined : unit -> unit

(** Determine if base (0) or step (1) has been fully refined *)
val is_not_fully_refined : int -> bool

(** Check if, following this refinement, the abstraction has been fully refined. *)
val check_fully_refined : int -> unit

(** Return the depth of the last refinement *)
val get_last_k_refined : unit -> int

(** Assign scores to variables (for heurisic refinements) *)
val score_variables : Types.foundvarstable -> Types.idtype list -> int -> Types.check_type -> in_channel -> unit
  
(** Determine if we should check for refinement on this step *)
val check_step_refinement : int -> bool

(** Perform a refinement on the current abstraction and unsat core variables.
May signal end of main loop. *)
val refine_abstraction : in_channel -> Types.defhashtable -> int -> Types.addtype -> bool -> Types.check_type -> Types.foundvarstable -> int -> Types.found_ids_and_steps -> Types.idtype list

(** Check to see if the counterexample given is valid -- if spurious, refine. *)
val check_and_refine_abstraction : in_channel -> Types.defhashtable -> int -> Types.addtype -> Types.check_type -> Types.foundvarstable -> Types.idtype list -> int -> Types.refine_return

(** Print out various stats (several pertain to refinement, so it's put here) *)
val print_stats : Types.defhashtable -> unit

